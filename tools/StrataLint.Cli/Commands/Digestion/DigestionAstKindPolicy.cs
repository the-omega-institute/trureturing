using System.Collections.Immutable;

namespace StrataLint.Cli;

internal static class DigestionAstKindPolicy
{
    internal static ImmutableArray<string> FormalizableKinds { get; } =
    [
        "theorem",
        "proposition",
        "lemma",
        "corollary",
        "定理",
        "命题",
        "引理",
        "推论",
    ];

    internal static ImmutableArray<string> NotFormalizableKinds { get; } =
    [
        "row",
        "v",
        "research-queue",
        "metadata",
        "negative-register",
        "M",
    ];

    private static readonly ImmutableHashSet<string> FormalizableKindSet =
        FormalizableKinds.ToImmutableHashSet(StringComparer.Ordinal);

    private static readonly ImmutableHashSet<string> NotFormalizableKindSet =
        NotFormalizableKinds.ToImmutableHashSet(StringComparer.Ordinal);

    internal static bool TryGetFormalizableKind(string astPath, out string kind) =>
        TryGetKind(astPath, out kind) && FormalizableKindSet.Contains(kind);

    internal static bool TryGetNotFormalizableKind(string astPath, out string kind) =>
        TryGetKind(astPath, out kind) && NotFormalizableKindSet.Contains(kind);

    private static bool TryGetKind(string astPath, out string kind)
    {
        var separator = astPath.IndexOf('/', StringComparison.Ordinal);
        if (separator <= 0)
        {
            kind = string.Empty;
            return false;
        }

        kind = astPath[..separator];
        return true;
    }
}
