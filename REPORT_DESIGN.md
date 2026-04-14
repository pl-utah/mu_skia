# Report System Design (Reusable Across Projects)

## Goal
Build a **generic reporting framework** that agents can reuse across projects where:
- benchmark/test inputs differ,
- statuses differ,
- metrics differ,
- table columns differ,
- and output pages need lightweight filtering/exploration.

This doc defines a stable architecture and extension points.

---

## 1) Core Principles

1. **Data first, UI second**
   - Always emit machine-readable JSON (`results.json`) first.
   - HTML is a rendering layer over that JSON.

2. **Pluggable schema**
   - Do not hardcode benchmark-specific fields into execution logic.
   - Use a common envelope + project-specific payload fields.

3. **Deterministic statuses**
   - Status assignment should be explicit and rule-based.
   - Keep status taxonomy configurable.

4. **Actionable diagnostics**
   - Preserve command, exit code, and trimmed logs.
   - Include first-error summary and full detail payload.

5. **Cheap portability**
   - Single Python entrypoint.
   - Zero framework web stack; static HTML output.

---

## 2) Recommended Architecture

## Runner (Execution Layer)
Responsibilities:
- discover workloads,
- run pipeline steps,
- capture timings and logs,
- classify status,
- write `results.json`.

### Suggested step model
```text
discover -> generate -> check -> postprocess
```
Each step returns:
- `ok: bool`
- `duration_sec: float`
- `stdout, stderr`
- `exit_code`
- `timeout: bool`

## Classifier (Status Layer)
Inputs:
- step outputs,
- optional content rules (regex markers in logs).

Outputs:
- canonical status (e.g. `pass`, `check_error`, `grind_timeout`, ...),
- short reason string.

## Renderer (Presentation Layer)
- reads `results.json`,
- renders HTML summary cards + table,
- no project-specific execution logic.

---

## 3) Data Contract (JSON)

Use this envelope:

```json
{
  "started_at": "ISO-8601",
  "finished_at": "ISO-8601",
  "runner_version": "string",
  "project": "string",
  "timeout_seconds": 120,
  "columns": ["name", "status", "check_seconds"],
  "statuses": ["pass", "check_error"],
  "results": [
    {
      "id": "benchmark_or_case_name",
      "status": "pass",
      "metrics": {"generate_seconds": 0.2, "check_seconds": 4.1},
      "artifacts": {"primary_file": "path/to/file"},
      "summary": "first error line or short success note",
      "details": "trimmed stdout/stderr"
    }
  ]
}
```

Notes:
- `metrics` and `artifacts` are intentionally open-ended.
- `columns` tells renderer what to display by default.

---

## 4) Status Design

Status sets vary per project; define them in config, not code constants.

Example groups:
- success: `pass`
- infra: `timeout_generate`, `timeout_check`, `runner_error`
- compiler: `generate_error`, `parse_error`
- prover: `check_error`, `grind_timeout`, `unknown_constant`

Recommended: map statuses to semantic buckets for consistent coloring:
- green: success
- amber: timeouts/resource limits
- red: functional failures
- gray: skipped/missing

---

## 5) Table Column Strategy

Columns should be configurable, with each column descriptor containing:
- `key`
- `label`
- `type` (`text|number|status|path|details`)
- `sortable` (bool)
- optional formatter (e.g. seconds with 2 decimals)

For this repo’s TV use case, useful default columns:
- name/id
- status
- generate_seconds
- check_seconds
- total_seconds
- primary artifact path
- details (collapsible)

---

## 6) Filtering UX (Important)

Minimum features:
- case-insensitive substring search,
- OR query via `|` separator.

Example:
- `timeout|mail_ru|overlay` shows rows matching any term.

Future extensions:
- AND via `&`
- negation via `!term`
- field filters (`status:check_error`)

---

## 7) Scalability / Performance

When dataset grows:
- write one JSON, avoid embedding massive logs inline by default,
- optionally move per-row logs to separate files,
- support pagination or lazy row rendering in HTML,
- parallelize runner with bounded workers.

---

## 8) Operational Checklist for New Project

1. Define pipeline steps.
2. Define status taxonomy + classifier rules.
3. Define metric keys and table columns.
4. Implement runner adapters (commands/tools).
5. Emit `results.json` in common envelope.
6. Reuse generic renderer template.
7. Validate with a small sample and one known failure case.

---

## 9) Current Repo Notes

Current implementation (`benchmark_report.py`) already supports:
- static HTML + JSON artifacts,
- per-step timing,
- status cards,
- log details,
- OR filtering with `|`.

Next easy upgrades:
- status-specific regex classification plugin file,
- sortable headers,
- export CSV from `results.json`.
