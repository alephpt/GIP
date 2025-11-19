#!/bin/bash
# GIP Definitive Metrics Generator
# Run from project root: ./scripts/metrics.sh

set -e

OUTPUT_FILE="METRICS_$(date -I).txt"

echo "=== GIP DEFINITIVE METRICS ===" | tee "$OUTPUT_FILE"
echo "Date: $(date -I)" | tee -a "$OUTPUT_FILE"
echo "" | tee -a "$OUTPUT_FILE"

# 1. Lines of Code
echo "Lines of Code:" | tee -a "$OUTPUT_FILE"
find Gip -name "*.lean" -exec wc -l {} + | tail -1 | tee -a "$OUTPUT_FILE"

# 2. Theorem count
echo "" | tee -a "$OUTPUT_FILE"
echo "Theorems:" | tee -a "$OUTPUT_FILE"
rg "^theorem " Gip --type lean | wc -l | tee -a "$OUTPUT_FILE"

# 3. Axiom count
echo "" | tee -a "$OUTPUT_FILE"
echo "Axioms:" | tee -a "$OUTPUT_FILE"
rg "^axiom " Gip --type lean | wc -l | tee -a "$OUTPUT_FILE"

# 4. Sorry count (actual, not comments)
echo "" | tee -a "$OUTPUT_FILE"
echo "Sorry statements:" | tee -a "$OUTPUT_FILE"
SORRY_COUNT=$(rg "^\s*sorry\s*$" Gip --type lean | wc -l)
echo "${SORRY_COUNT}" | tee -a "$OUTPUT_FILE"

# 5. Build status
echo "" | tee -a "$OUTPUT_FILE"
echo "Build status:" | tee -a "$OUTPUT_FILE"
lake build 2>&1 | grep "Build completed" | tee -a "$OUTPUT_FILE" || echo "FAILED" | tee -a "$OUTPUT_FILE"

# 6. Module count
echo "" | tee -a "$OUTPUT_FILE"
echo "Modules:" | tee -a "$OUTPUT_FILE"
find Gip -name "*.lean" | wc -l | tee -a "$OUTPUT_FILE"

# 7. Documentation pages
echo "" | tee -a "$OUTPUT_FILE"
echo "Documentation pages:" | tee -a "$OUTPUT_FILE"
find docs -name "*.md" 2>/dev/null | wc -l | tee -a "$OUTPUT_FILE"

echo "" | tee -a "$OUTPUT_FILE"
echo "Saved to: $OUTPUT_FILE" | tee -a "$OUTPUT_FILE"