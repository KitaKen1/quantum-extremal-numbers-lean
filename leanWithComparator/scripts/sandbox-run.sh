#!/usr/bin/env bash
# Run only on Linux, as the current unprivileged user, with real Landrun.
set -euo pipefail
: "${COMPARATOR_TOOLS:?Run install-tools.sh first}"
test "$(uname -s)" = Linux
test "$(id -u)" -ne 0
QEX_PROJECT=$1
QEX_CONFIG=$2
QEX_LOG=$3
mkdir -p "$(dirname -- "$QEX_LOG")"
sudo systemd-run --wait --collect --pipe \
  --uid="$(id -u)" --gid="$(id -g)" \
  --property='RestrictAddressFamilies=~AF_UNIX' --property=NoNewPrivileges=yes \
  --property=RuntimeMaxSec=45min --working-directory="$QEX_PROJECT" \
  --setenv="PATH=$HOME/.elan/bin:$PATH" --setenv="HOME=$HOME" \
  --setenv="COMPARATOR_LANDRUN=$COMPARATOR_TOOLS/bin/landrun" \
  --setenv="COMPARATOR_LEAN4EXPORT=$COMPARATOR_TOOLS/lean4export/.lake/build/bin/lean4export" \
  -- "$HOME/.elan/bin/lake" env "$COMPARATOR_TOOLS/comparator/.lake/build/bin/comparator" "$QEX_CONFIG" \
  2>&1 | tee "$QEX_LOG"
