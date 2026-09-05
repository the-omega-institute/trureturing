#!/usr/bin/env bash
# Scan every tracked judge-surface file of a tree with the SL-030 scanner built in that tree,
# exactly as the admission judge would when the rule implementation is in the candidate delta
# (every judge-surface file is re-judged then). Prints each finding; exit 1 if there is any.
#
# Usage: tools/scripts/agent/sl030-real-surface.sh <tree-root>
#
# Run this after any change to the invocation-discovery or option rules and before pushing:
# review round 15 found 13 false positives on the real surface that the synthetic matrix could
# not see (CLAUDE.md 器律⑦′ forbids tests over real workflow content, so this is a tracked
# run-local probe (器律⑨), not a test). It needs `make -C tools dotnet` to have built the Engine.
set -euo pipefail

root=$(cd "${1:?usage: sl030-real-surface.sh <tree-root>}" && pwd)
# The CLI's output directory carries the Engine together with every dependency it loads
# (YamlDotNet, Tomlyn, …); Assembly.LoadFrom resolves siblings from there.
dll=$(ls "$root"/tools/StrataLint.Cli/bin/Release/net*/StrataLint.Engine.dll 2>/dev/null | head -1)
[ -n "$dll" ] || { echo "sl030-real-surface: no built StrataLint.Engine.dll under the CLI output of $root (run make -C tools dotnet)" >&2; exit 64; }

probe=$(mktemp -d "${TMPDIR:-/tmp}/sl030-probe.XXXXXX")
trap 'rm -rf "$probe"' EXIT
cat > "$probe/Probe.csproj" <<'EOF'
<Project Sdk="Microsoft.NET.Sdk">
  <PropertyGroup>
    <OutputType>Exe</OutputType>
    <TargetFramework>net10.0</TargetFramework>
    <Nullable>enable</Nullable>
    <ImplicitUsings>enable</ImplicitUsings>
  </PropertyGroup>
</Project>
EOF
cat > "$probe/Program.cs" <<'EOF'
using System.Collections;
using System.Reflection;

var dll = args[0];
var root = args[1];
var assembly = Assembly.LoadFrom(dll);
var scanner = assembly.GetType("StrataLint.Engine.JudgeSurfaceRevisionScanner")
    ?? throw new InvalidOperationException("JudgeSurfaceRevisionScanner not found");
var isSurface = scanner.GetMethod("IsJudgeSurfacePath", BindingFlags.NonPublic | BindingFlags.Static)
    ?? throw new InvalidOperationException("IsJudgeSurfacePath not found");
var scan = scanner.GetMethod("Scan", BindingFlags.NonPublic | BindingFlags.Static)
    ?? throw new InvalidOperationException("Scan not found");
var files = 0;
var findings = 0;
foreach (var path in Console.In.ReadToEnd().Split('\n', StringSplitOptions.RemoveEmptyEntries))
{
    if (!(bool)isSurface.Invoke(null, new object[] { path })!)
    {
        continue;
    }

    files++;
    var text = File.ReadAllText(Path.Combine(root, path));
    foreach (var message in (IEnumerable)scan.Invoke(null, new object[] { path, text })!)
    {
        findings++;
        Console.WriteLine($"SL-030 {path}: {message}");
    }
}

Console.WriteLine($"REAL_SURFACE_RESULT files={files} findings={findings}");
return findings == 0 ? 0 : 1;
EOF
(cd "$probe" && dotnet build -c Release --nologo -v q >/dev/null)
git -C "$root" ls-files | dotnet "$probe/bin/Release/net10.0/Probe.dll" "$dll" "$root"
