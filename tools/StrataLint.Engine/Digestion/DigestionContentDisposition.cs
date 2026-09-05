using System.Collections.Immutable;

namespace StrataLint.Engine;

internal enum DigestionContentRole
{
    FormalizableClaim,
    NotFormalizable,
}

internal static class DigestionContentDisposition
{
    private static readonly ImmutableHashSet<string> ProducerLocatorKinds =
        ImmutableHashSet.Create(
            StringComparer.Ordinal,
            "appendix",
            "assembly-volume",
            "audit",
            "chain-court",
            "classical",
            "coarse",
            "cone-engine",
            "constant",
            "contraction-spectrum",
            "crystallization",
            "diagonal-ledger",
            "dual-heights",
            "duality",
            "entanglement",
            "entropy",
            "entropy-relativity",
            "final-volume",
            "formal-volume",
            "freedom",
            "interface",
            "item",
            "ledger-axioms",
            "ledger-machine",
            "machine-negations",
            "measurement",
            "memory",
            "metadata",
            "metric-rates",
            "modular-time",
            "mountainside",
            "nameability",
            "negative-register",
            "observer",
            "observer-clock",
            "ontology",
            "open",
            "path-divergence",
            "pen-down",
            "periodic-table",
            "physics",
            "premise",
            "probability",
            "quotient-court",
            "research-boundary",
            "research-queue",
            "row",
            "scope",
            "section",
            "semantic-court",
            "shadow",
            "shadow-tax",
            "six-questions",
            "stationary-points",
            "synthesis",
            "tower-top",
            "trace-note",
            "verdict",
            "version");

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
            .Concat(ProducerLocatorKinds)
            .Concat(FormalizableKinds)
            .Append("none")
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

        if (KnownKindLabels.Contains(kind, StringComparer.Ordinal)
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
