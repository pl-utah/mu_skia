#!/usr/bin/env bash
set -euo pipefail

REPORT_DIR="${REPORT_DIR:-/artifacts}"

echo "Running lake build"
lake build

echo "Running TV on pinterest.com__layer_97"
uv run python make_report.py \
    --optj-dir optj_100 \
    --report-dir "$REPORT_DIR" \
    --filter pinterest.com__layer_97 \
    --no-report
