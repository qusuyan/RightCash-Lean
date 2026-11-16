# Source this to put the project-local Lean toolchain on PATH:
#   source ./env.sh && lake build
export PATH="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/.toolchain/lean-4.35.0-linux/bin:$PATH"
