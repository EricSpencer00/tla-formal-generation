#!/usr/bin/env bash
set -euo pipefail

BASE_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TOOLS_DIR="$BASE_DIR/tools"
JAR_URL="https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar"
JAR_PATH="$TOOLS_DIR/tla2tools.jar"

mkdir -p "$TOOLS_DIR"
if [ -f "$JAR_PATH" ]; then
  echo "tla2tools.jar already exists at $JAR_PATH"
  exit 0
fi

echo "Downloading tla2tools.jar from $JAR_URL..."
curl -L -o "$JAR_PATH" "$JAR_URL"
chmod 644 "$JAR_PATH"

echo "Downloaded to $JAR_PATH"

echo "You can run TLC with: java -cp $JAR_PATH tlc2.TLC <Module>"