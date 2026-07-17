#!/usr/bin/env bash
set -euo pipefail

REPORT_DIR="${REPORT_DIR:-/artifacts}"

echo "Running lake build"
lake build

echo "Running TV on all benchmarks"
uv run python make_report.py \
    --optj-dir optj_100 \
    --report-dir "$REPORT_DIR"
