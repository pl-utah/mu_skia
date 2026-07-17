#!/usr/bin/env bash
set -euo pipefail

REPORT_DIR="${REPORT_DIR:-/artifacts}"

lake build

uv run python make_report.py \
    --optj-dir optj_100 \
    --report-dir "$REPORT_DIR" \
    --filter pinterest.com__layer_97 \
    --no-report
