using System.Collections.Immutable;

namespace StrataLint.Engine;

internal enum DigestionContentRole
{
    FormalizableClaim,
    NotFormalizable,
}

internal static class DigestionContentDisposition
{
    private static readonly ImmutableHashSet<string> FormalizableKinds =
        ImmutableHashSet.Create(
            StringComparer.Ordinal,
            "theorem",
            "proposition",
            "lemma",
            "corollary",
            "theorem-form",
            "定理",
            "命题",
            "引理",
            "推论",
            "候签定理");

    internal static ImmutableArray<string> KnownKindLabels { get; } =
        TheoryAtomizerRules.AllowedKinds
            .Concat(FormalizableKinds)
            .Distinct(StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .ToImmutableArray();

    internal static (DigestionContentRole Role, string KindLabel) Resolve(string? kind)
    {
        if (kind is null)
        {
            return (DigestionContentRole.NotFormalizable, "none");
        }

        if (FormalizableKinds.Contains(kind))
        {
            return (DigestionContentRole.FormalizableClaim, kind);
        }

        if (TheoryAtomizerRules.AllowedKinds.Contains(kind)
            || kind.StartsWith("unregistered:", StringComparison.Ordinal)
                && kind.Length > "unregistered:".Length)
        {
            return (DigestionContentRole.NotFormalizable, kind);
        }

        throw new FormatException($"content kind '{kind}' has no disposition");
    }

    internal static string NormalizeNumberedClaimToken(string token) =>
        KnownKindLabels.Contains(token, StringComparer.Ordinal)
            ? token
            : Unregistered(token);

    internal static string Unregistered(string token) => "unregistered:" + token;
}
