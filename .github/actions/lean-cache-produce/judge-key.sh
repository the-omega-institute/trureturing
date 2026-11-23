#!/usr/bin/env bash
set -euo pipefail

sdk="$(dotnet --version)"
[[ "$sdk" =~ ^[0-9]+\.[0-9]+\.[0-9]+ ]] || { echo "unexpected SDK version '$sdk'" >&2; exit 2; }
recipe="$(python3 tools/scripts/workflow/ci_checks.py judge-recipe | sha256sum | cut -c1-16)"
inputs=(Meta/tools-release.json .editorconfig .globalconfig 'Directory.Build.*' Directory.Packages.props
        NuGet.Config NuGet.config nuget.config global.json)
listing="$(mktemp)"
trap 'rm -f "$listing"' EXIT
git ls-files -s -z -- "${inputs[@]/#/:(glob)}" > "$listing"
[[ -s "$listing" ]] || { echo 'judge inputs select no tracked file' >&2; exit 2; }
digest="$(sha256sum < "$listing" | cut -c1-64)"
echo "key=judge-${RUNNER_OS:?}-${RUNNER_ARCH:?}-sdk$sdk-$recipe-$digest"
