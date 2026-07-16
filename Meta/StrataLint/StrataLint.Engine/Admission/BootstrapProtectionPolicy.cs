using System.Collections.Immutable;

namespace StrataLint.Engine;

internal enum ProtectionMatchKind
{
    Exact,
    Prefix,
    Suffix,
    Contains,
}

internal enum ProtectionComparison
{
    Ordinal,
    OrdinalIgnoreCase,
}

internal sealed record ProtectionMatcher(
    string Id,
    ProtectionMatchKind Kind,
    string Pattern,
    ProtectionComparison Comparison)
{
    internal bool Matches(string value)
    {
        var comparison = Comparison is ProtectionComparison.Ordinal
            ? StringComparison.Ordinal
            : StringComparison.OrdinalIgnoreCase;
        return Kind switch
        {
            ProtectionMatchKind.Exact => string.Equals(value, Pattern, comparison),
            ProtectionMatchKind.Prefix => value.StartsWith(Pattern, comparison),
            ProtectionMatchKind.Suffix => value.EndsWith(Pattern, comparison),
            ProtectionMatchKind.Contains => value.Contains(Pattern, comparison),
            _ => throw new InvalidOperationException("unknown protection match kind"),
        };
    }
}

internal static class BootstrapProtectionPolicy
{
    internal static ImmutableArray<ProtectionMatcher> Matchers { get; } =
    [
        Atom("meta-stratalint", ProtectionMatchKind.Prefix, "Meta/StrataLint/"),
        Atom("contract-epoch", ProtectionMatchKind.Prefix, "Meta/contract-epoch/"),
        Atom("specification", ProtectionMatchKind.Exact, BootstrapGate.SpecificationPath),
        Atom("registry", ProtectionMatchKind.Exact, "Meta/registry.yaml"),
        Atom("domains", ProtectionMatchKind.Exact, "Meta/domains.yaml"),
        Atom("hearts", ProtectionMatchKind.Suffix, "/Hearts.lean"),
        Atom("assumptions", ProtectionMatchKind.Contains, "/X_Assumptions/"),
        Atom(
            "meta-golden",
            ProtectionMatchKind.Prefix,
            "Meta/golden/",
            ProtectionComparison.OrdinalIgnoreCase),
        Atom(
            "golden-segment",
            ProtectionMatchKind.Contains,
            "/Golden/",
            ProtectionComparison.OrdinalIgnoreCase),
        Atom("solution", ProtectionMatchKind.Suffix, ".sln"),
        Atom("solution-xml", ProtectionMatchKind.Suffix, ".slnx"),
        Atom("project", ProtectionMatchKind.Suffix, ".csproj"),
        Atom("scribe-source", ProtectionMatchKind.Suffix, ".scribe.cs"),
        Atom("makefile", ProtectionMatchKind.Exact, "Makefile"),
        Atom("dotnet-sdk", ProtectionMatchKind.Exact, "global.json"),
        Atom("directory-build", ProtectionMatchKind.Prefix, "Directory.Build."),
        Atom("directory-packages", ProtectionMatchKind.Prefix, "Directory.Packages."),
        Atom("package-lock", ProtectionMatchKind.Suffix, "packages.lock.json"),
        Atom(
            "nuget-config",
            ProtectionMatchKind.Suffix,
            "NuGet.Config",
            ProtectionComparison.OrdinalIgnoreCase),
        Atom("lean-toolchain", ProtectionMatchKind.Exact, "lean-toolchain"),
        Atom("lakefile", ProtectionMatchKind.Exact, "lakefile.toml"),
        Atom("lake-manifest", ProtectionMatchKind.Exact, "lake-manifest.json"),
        Atom("codeowners", ProtectionMatchKind.Exact, ".github/CODEOWNERS"),
        Atom("workflows", ProtectionMatchKind.Prefix, ".github/workflows/"),
        Atom("github-scripts", ProtectionMatchKind.Prefix, ".github/scripts/"),
    ];

    internal static ImmutableArray<string> ExactExclusions { get; } =
    [
        "Meta/StrataLint/Golden/cases/digestion-and-anchors.toml",
        "Meta/StrataLint/Golden/cases/protected-semantics.toml",
        "Meta/StrataLint/Golden/cases/structure-and-identities.toml",
        "Meta/StrataLint/Golden/cases/structured-ledger.toml",
        "Meta/StrataLint/Golden/values-kernels.toml",
    ];

    internal static ImmutableArray<string> LegacyPrefixExclusions { get; } =
    [
        BootstrapGate.DefinitionsPathPrefix,
    ];

    internal static bool IsProtected(RepoPath path) =>
        IsProtected(path.Value, Matchers, ExactExclusions, LegacyPrefixExclusions);

    internal static bool IsProtected(
        string value,
        ImmutableArray<ProtectionMatcher> matchers,
        ImmutableArray<string> exactExclusions,
        ImmutableArray<string> legacyPrefixExclusions)
    {
        if (exactExclusions.Contains(value, StringComparer.Ordinal)
            || legacyPrefixExclusions.Any(prefix => value.StartsWith(prefix, StringComparison.Ordinal)))
        {
            return false;
        }

        return matchers.Any(matcher => matcher.Matches(value));
    }

    private static ProtectionMatcher Atom(
        string id,
        ProtectionMatchKind kind,
        string pattern,
        ProtectionComparison comparison = ProtectionComparison.Ordinal) =>
        new(id, kind, pattern, comparison);
}
