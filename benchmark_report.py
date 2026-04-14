#!/usr/bin/env python3
from __future__ import annotations

import argparse
import html
import json
import subprocess
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import asdict, dataclass
from datetime import datetime
from pathlib import Path
from typing import Literal

Status = Literal[
    "pass",
    "timeout_generate",
    "timeout_check",
    "generate_error",
    "grind_timeout",
    "check_error",
    "missing_inputs",
]


@dataclass
class BenchmarkResult:
    name: str
    status: Status
    generate_seconds: float
    check_seconds: float
    total_seconds: float
    lean_file: str
    details: str


REQUIRED_SUFFIXES = ["", ".01", ".02", ".03", ".04"]


def expected_files(layer_dir: Path, name: str) -> list[Path]:
    return [layer_dir / f"{name}{suffix}.json" for suffix in REQUIRED_SUFFIXES]


def run_cmd(command: list[str], timeout: int | None) -> tuple[int, str, str, float, bool]:
    start = time.time()
    try:
        proc = subprocess.run(command, capture_output=True, text=True, timeout=timeout)
        elapsed = time.time() - start
        return proc.returncode, proc.stdout, proc.stderr, elapsed, False
    except subprocess.TimeoutExpired as e:
        elapsed = time.time() - start
        out = e.stdout or ""
        err = e.stderr or ""
        return 124, out, err, elapsed, True


def is_grind_timeout(output: str) -> bool:
    s = output.lower()
    if "`grind` failed" not in s and "grind failed" not in s:
        return False
    timeout_markers = [
        "[limits]",
        "maximum number of heartbeats",
        "heartbeats",
        "resource limit",
        "time limit",
        "timeout",
        "threshold: `(gen",
        "threshold: `(e-matching",
    ]
    return any(m in s for m in timeout_markers)


def trim_output(s: str, max_chars: int = 5000) -> str:
    if len(s) <= max_chars:
        return s
    return s[: max_chars - 50] + "\n... <truncated> ...\n"


def run_one(name: str, optj_dir: Path, report_dir: Path, timeout: int | None) -> BenchmarkResult:
    layer_dir = optj_dir / name
    inputs = expected_files(layer_dir, name)
    lean_path = report_dir / "generated" / f"Generated_{name}.lean"

    if not all(p.exists() for p in inputs):
        missing = [str(p) for p in inputs if not p.exists()]
        return BenchmarkResult(
            name=name,
            status="missing_inputs",
            generate_seconds=0.0,
            check_seconds=0.0,
            total_seconds=0.0,
            lean_file=str(lean_path),
            details="Missing inputs:\n" + "\n".join(missing),
        )

    lean_path.parent.mkdir(parents=True, exist_ok=True)

    # 1) Generate Lean file
    gen_cmd = ["uv", "run", "python", "lean_compiler.py", name]
    rc, out, err, gen_sec, timed_out = run_cmd(gen_cmd, timeout)

    if timed_out:
        return BenchmarkResult(
            name=name,
            status="timeout_generate",
            generate_seconds=gen_sec,
            check_seconds=0.0,
            total_seconds=gen_sec,
            lean_file=str(lean_path),
            details=f"Command timed out: {' '.join(gen_cmd)}\n\nSTDOUT:\n{trim_output(out)}\nSTDERR:\n{trim_output(err)}",
        )

    if rc != 0:
        return BenchmarkResult(
            name=name,
            status="generate_error",
            generate_seconds=gen_sec,
            check_seconds=0.0,
            total_seconds=gen_sec,
            lean_file=str(lean_path),
            details=f"Generate failed (exit {rc})\nCommand: {' '.join(gen_cmd)}\n\nSTDOUT:\n{trim_output(out)}\nSTDERR:\n{trim_output(err)}",
        )

    lean_path.write_text(out)

    # 2) Typecheck generated file
    check_cmd = ["lake", "env", "lean", str(lean_path)]
    rc2, out2, err2, check_sec, timed_out2 = run_cmd(check_cmd, timeout)

    total = gen_sec + check_sec
    if timed_out2:
        return BenchmarkResult(
            name=name,
            status="timeout_check",
            generate_seconds=gen_sec,
            check_seconds=check_sec,
            total_seconds=total,
            lean_file=str(lean_path),
            details=f"Command timed out: {' '.join(check_cmd)}\n\nSTDOUT:\n{trim_output(out2)}\nSTDERR:\n{trim_output(err2)}",
        )

    if rc2 != 0:
        combined = (out2 or "") + "\n" + (err2 or "")
        status: Status = "grind_timeout" if is_grind_timeout(combined) else "check_error"
        return BenchmarkResult(
            name=name,
            status=status,
            generate_seconds=gen_sec,
            check_seconds=check_sec,
            total_seconds=total,
            lean_file=str(lean_path),
            details=f"Typecheck failed (exit {rc2})\nCommand: {' '.join(check_cmd)}\n\nSTDOUT:\n{trim_output(out2)}\nSTDERR:\n{trim_output(err2)}",
        )

    details = trim_output((out2 + "\n" + err2).strip())
    return BenchmarkResult(
        name=name,
        status="pass",
        generate_seconds=gen_sec,
        check_seconds=check_sec,
        total_seconds=total,
        lean_file=str(lean_path),
        details=details,
    )


def make_html(results: list[BenchmarkResult], started_at: str, timeout: int | None) -> str:
    total = len(results)
    counts: dict[str, int] = {}
    for r in results:
        counts[r.status] = counts.get(r.status, 0) + 1

    def c(k: str) -> int:
        return counts.get(k, 0)

    timeout_label = f"{timeout}s" if timeout is not None else "none (use Lean/grind internal limits)"

    rows = []
    for r in results:
        cls = r.status
        rows.append(
            "<tr>"
            f"<td>{html.escape(r.name)}</td>"
            f"<td class='status {cls}'>{html.escape(r.status)}</td>"
            f"<td>{r.generate_seconds:.2f}</td>"
            f"<td>{r.check_seconds:.2f}</td>"
            f"<td>{r.total_seconds:.2f}</td>"
            f"<td><code>{html.escape(r.lean_file)}</code></td>"
            f"<td><details><summary>log</summary><pre>{html.escape(r.details)}</pre></details></td>"
            "</tr>"
        )

    return f"""<!doctype html>
<html lang='en'>
<head>
  <meta charset='utf-8' />
  <meta name='viewport' content='width=device-width,initial-scale=1' />
  <title>LambdaSkia TV Benchmark Report</title>
  <style>
    body {{ font-family: -apple-system, BlinkMacSystemFont, Segoe UI, Roboto, sans-serif; margin: 24px; }}
    h1 {{ margin-bottom: 8px; }}
    .meta {{ color: #555; margin-bottom: 16px; }}
    .cards {{ display: flex; gap: 10px; flex-wrap: wrap; margin-bottom: 16px; }}
    .card {{ border: 1px solid #ddd; border-radius: 8px; padding: 10px 14px; min-width: 120px; }}
    table {{ border-collapse: collapse; width: 100%; font-size: 14px; }}
    th, td {{ border: 1px solid #e6e6e6; padding: 8px; vertical-align: top; }}
    th {{ background: #fafafa; position: sticky; top: 0; }}
    .status {{ font-weight: 600; text-transform: lowercase; }}
    .pass {{ color: #106b21; }}
    .timeout_generate, .timeout_check, .grind_timeout {{ color: #9a6700; }}
    .generate_error, .check_error, .missing_inputs {{ color: #b42318; }}
    pre {{ white-space: pre-wrap; max-width: 900px; }}
    input {{ padding: 6px; width: 280px; }}
  </style>
</head>
<body>
  <h1>LambdaSkia TV Benchmark Report</h1>
  <div class='meta'>Started: {html.escape(started_at)} | Benchmarks: {total} | Subprocess timeout: {html.escape(timeout_label)}</div>

  <div class='cards'>
    <div class='card'><div>Total</div><strong>{total}</strong></div>
    <div class='card'><div>Pass</div><strong>{c('pass')}</strong></div>
    <div class='card'><div>Timeout (gen)</div><strong>{c('timeout_generate')}</strong></div>
    <div class='card'><div>Timeout (check)</div><strong>{c('timeout_check')}</strong></div>
    <div class='card'><div>Gen error</div><strong>{c('generate_error')}</strong></div>
    <div class='card'><div>Grind timeout</div><strong>{c('grind_timeout')}</strong></div>
    <div class='card'><div>Check error</div><strong>{c('check_error')}</strong></div>
    <div class='card'><div>Missing inputs</div><strong>{c('missing_inputs')}</strong></div>
  </div>

  <div style='margin-bottom:10px;'>
    <label>Filter name/status: <input id='q' placeholder='e.g. Zen_News|timeout|overlay' /></label>
  </div>

  <table id='t'>
    <thead>
      <tr>
        <th>Name</th>
        <th>Status</th>
        <th data-sort-method='number'>Gen (s)</th>
        <th data-sort-method='number'>Check (s)</th>
        <th data-sort-method='number'>Total (s)</th>
        <th>Lean file</th>
        <th>Details</th>
      </tr>
    </thead>
    <tbody>
      {''.join(rows)}
    </tbody>
  </table>

  <script src='https://unpkg.com/tablesort@5.3.0/dist/tablesort.min.js'></script>
  <script>
    const table = document.getElementById('t');
    new Tablesort(table);

    const q = document.getElementById('q');
    const rows = Array.from(document.querySelectorAll('#t tbody tr'));

    function visibleByQuery(rowText, query) {{
      const raw = query.trim().toLowerCase();
      if (!raw) return true;
      // OR semantics with `|`, e.g. "timeout|mail_ru|overlay"
      const terms = raw.split('|').map(s => s.trim()).filter(Boolean);
      if (terms.length === 0) return true;
      return terms.some(t => rowText.includes(t));
    }}

    q.addEventListener('input', () => {{
      const query = q.value;
      for (const r of rows) {{
        const txt = r.innerText.toLowerCase();
        r.style.display = visibleByQuery(txt, query) ? '' : 'none';
      }}
    }});
  </script>
</body>
</html>
"""


def main() -> None:
    parser = argparse.ArgumentParser(description="Run TV over all optj benchmarks and generate HTML report")
    parser.add_argument("--optj-dir", type=Path, default=Path("optj"))
    parser.add_argument("--report-dir", type=Path, default=Path("report"))
    parser.add_argument(
        "--timeout",
        type=int,
        default=0,
        help="Subprocess timeout per step in seconds (0 disables wrapper timeout and relies on Lean/grind limits)",
    )
    parser.add_argument("--only", nargs="*", default=None, help="Optional explicit benchmark names")
    parser.add_argument("--workers", type=int, default=1, help="Number of benchmarks to run in parallel")
    args = parser.parse_args()

    if args.only:
        names = args.only
    else:
        names = sorted([p.name for p in args.optj_dir.iterdir() if p.is_dir()])

    args.report_dir.mkdir(parents=True, exist_ok=True)
    (args.report_dir / "generated").mkdir(parents=True, exist_ok=True)

    started_at = datetime.now().isoformat(timespec="seconds")
    results: list[BenchmarkResult] = []

    timeout_value: int | None = args.timeout if args.timeout > 0 else None
    timeout_label = f"{timeout_value}s" if timeout_value is not None else "none"

    workers = max(1, args.workers)
    print(f"Running {len(names)} benchmarks (subprocess-timeout={timeout_label}, workers={workers})...")

    if workers == 1:
        for i, name in enumerate(names, start=1):
            print(f"[{i}/{len(names)}] {name}")
            r = run_one(name, args.optj_dir, args.report_dir, timeout_value)
            results.append(r)
            print(f"  -> {r.status} (gen={r.generate_seconds:.2f}s, check={r.check_seconds:.2f}s)")
    else:
        indexed_names = list(enumerate(names, start=1))
        by_name: dict[str, BenchmarkResult] = {}
        with ThreadPoolExecutor(max_workers=workers) as ex:
            fut_to_info = {
                ex.submit(run_one, name, args.optj_dir, args.report_dir, timeout_value): (idx, name)
                for idx, name in indexed_names
            }
            done = 0
            for fut in as_completed(fut_to_info):
                idx, name = fut_to_info[fut]
                r = fut.result()
                by_name[name] = r
                done += 1
                print(
                    f"[{done}/{len(names)} done] ({idx}/{len(names)}) {name}"
                    f" -> {r.status} (gen={r.generate_seconds:.2f}s, check={r.check_seconds:.2f}s)"
                )

        # Preserve deterministic output order
        results = [by_name[name] for name in names]

    # Write machine-readable artifact
    report_json = {
        "started_at": started_at,
        "timeout_seconds": timeout_value,
        "total": len(results),
        "results": [asdict(r) for r in results],
    }
    (args.report_dir / "results.json").write_text(json.dumps(report_json, indent=2))

    # Write HTML dashboard
    (args.report_dir / "index.html").write_text(make_html(results, started_at, timeout_value))

    print(f"\nReport written to: {args.report_dir / 'index.html'}")
    print(f"JSON written to:   {args.report_dir / 'results.json'}")


if __name__ == "__main__":
    main()
