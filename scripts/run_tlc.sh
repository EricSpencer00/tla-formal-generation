#!/usr/bin/env bash
set -euo pipefail

if [ $# -lt 1 ]; then
  echo "Usage: $0 <ModuleNameWithoutTLA> [cfg-file]"
  exit 2
fi
MODULE="$1"
CFG_ARG="${2:-}"
BASE_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
JAR="$BASE_DIR/tools/tla2tools.jar"

if [ ! -f "$JAR" ]; then
  echo "tla2tools.jar not found. Run scripts/install_tla2tools.sh first."
  exit 1
fi

# Resolve TLA file path: check repo root, samples/ and cwd
TLA_PATH_CANDIDATES=("$BASE_DIR/$MODULE.tla" "$BASE_DIR/samples/$MODULE.tla" "./$MODULE.tla")
TLA_PATH=""
for c in "${TLA_PATH_CANDIDATES[@]}"; do
  if [ -f "$c" ]; then
    TLA_PATH="$c"
    break
  fi
done
if [ -z "$TLA_PATH" ]; then
  echo "Could not find $MODULE.tla in repo root, samples/ or current dir."
  exit 2
fi

# Resolve CFG path: use provided arg, otherwise look near the tla file or in repo root
if [ -n "$CFG_ARG" ]; then
  CFG_PATH="$CFG_ARG"
else
  CFG_CANDIDATES=("$BASE_DIR/$MODULE.cfg" "$BASE_DIR/samples/$MODULE.cfg" "./$MODULE.cfg")
  CFG_PATH=""
  for c in "${CFG_CANDIDATES[@]}"; do
    if [ -f "$c" ]; then
      CFG_PATH="$c"
      break
    fi
  done
  if [ -z "$CFG_PATH" ]; then
    echo "Could not find $MODULE.cfg; please provide cfg path as second argument."
    exit 3
  fi
fi

java -cp "$JAR" tlc2.TLC -deadlock -config "$CFG_PATH" "$TLA_PATH"
