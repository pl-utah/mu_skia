#!/usr/bin/env bash
set -euo pipefail

REPO_DIR="${HOME_DIR:-$HOME}/mu_skia"
REPORT_DIR="${REPORT_DIR:-/artifacts}"

cd "$REPO_DIR"

uv run python make_report.py \
    --optj-dir optj_100 \
    --report-dir "$REPORT_DIR" \
    --filter pinterest.com__layer_97 \
    --no-report
