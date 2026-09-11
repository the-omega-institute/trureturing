namespace StrataLint.Engine;

internal static class FrozenLedgerDeltaPredicate
{
    internal static bool IsEnvironmentInput(string path) =>
        path is "lean-toolchain"
            or "lakefile.toml"
            or "lakefile.lean"
            or "lake-manifest.json";

    internal static bool IsManagedLeanSource(string path) =>
        path == "Trureturing.lean"
        || path.StartsWith("D5/", StringComparison.Ordinal)
            && path.EndsWith(".lean", StringComparison.Ordinal);

    internal static bool IsDeltaDefinitionInput(string path) =>
        path is RepositoryPathPolicy.PrWorkflowPath
            or RepositoryPathPolicy.PushWorkflowPath
            or "tools/scripts/ci-stage.sh"
            or "tools/scripts/ci-build-outputs.targets"
            or "tools/scripts/workflow/ci.py"
            or "tools/scripts/report/lean-report-input.sh"
            or "tools/lean-inspector/Inspector.lean"
            or "Directory.Build.props"
            or "Directory.Build.targets"
            or "Directory.Packages.props"
            or "global.json"
            or "tools/StrataLint.Cli/StrataLint.Cli.csproj"
            or "tools/StrataLint.Cli/packages.lock.json"
            or "tools/StrataLint.Engine/StrataLint.Engine.csproj"
            or "tools/StrataLint.Engine/packages.lock.json"
        || path.StartsWith("tools/StrataLint.Cli/", StringComparison.Ordinal)
            && path.EndsWith(".cs", StringComparison.Ordinal)
        || path.StartsWith("tools/StrataLint.Engine/", StringComparison.Ordinal)
            && path.EndsWith(".cs", StringComparison.Ordinal)
        || path.StartsWith("tools/StrataLint.EngineeringScope/", StringComparison.Ordinal)
            && (path.EndsWith(".cs", StringComparison.Ordinal)
                || path.EndsWith(".csproj", StringComparison.Ordinal)
                || path.EndsWith("packages.lock.json", StringComparison.Ordinal));
}
