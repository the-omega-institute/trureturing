#!/usr/bin/env bash
set -euo pipefail

: "${RUNNER_OS:?}" "${RUNNER_ARCH:?}"
sdk="$(dotnet --version)"
[[ "$sdk" =~ ^[0-9]+\.[0-9]+\.[0-9]+ ]] || { echo "unexpected SDK version '$sdk'" >&2; exit 2; }
recipe="$(python3 tools/scripts/workflow/ci_checks.py judge-recipe | sha256sum | cut -c1-16)"
packages="$(dotnet nuget locals global-packages --list --force-english-output)"
[[ "$packages" == 'global-packages: /'* ]] || { echo 'Cannot resolve the global packages directory' >&2; exit 2; }
# Scribe's compiled analyzer metadata refers to this absolute directory.
package_location="$(printf '%s' "${packages#global-packages: }" | sha256sum | cut -c1-16)"
inputs=(Meta/tools-release.json .editorconfig .globalconfig 'Directory.Build.*' Directory.Packages.props
        NuGet.Config NuGet.config nuget.config global.json)
listing="$(mktemp)"
trap 'rm -f "$listing"' EXIT
git ls-files -s -z -- "${inputs[@]/#/:(glob)}" > "$listing"
[[ -s "$listing" ]] || { echo 'judge inputs select no tracked file' >&2; exit 2; }
digest="$(sha256sum < "$listing" | cut -c1-64)"
echo "key=judge-v2-${RUNNER_OS}-${RUNNER_ARCH}-sdk$sdk-$recipe-$package_location-$digest"
