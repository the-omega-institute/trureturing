using System.Collections.Immutable;

namespace StrataLint.Cli;

internal static class DigestionContentKindPolicy
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

    internal static bool IsFormalizable(string kind) => FormalizableKindSet.Contains(kind);

    internal static bool IsNotFormalizable(string kind) => NotFormalizableKindSet.Contains(kind);
}
