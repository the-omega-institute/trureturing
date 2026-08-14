using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Endpoints;

internal sealed class BernoulliBridgeVarianceDocument : IScribeDocumentDefinition
{
    private static Formula BridgeVariance(Formula t) => Seq(
        Operatorname, Grp(F.Id("Var")), Open,
        Operatorname, Grp(F.Id("id")), Comma, Sp,
        Operatorname, Grp(F.Id("Ber")), Open, D(1), Comma, Sp, D(0), Comma, Sp, t, Close,
        Close);

    private static Formula UnitIntervalBinder() => Seq(
        Forall, Sp, F.Id("t"), InMacro, OpenBracket, D(0), Comma, Sp, D(1), CloseBracket,
        Comma, Esc);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Bernoulli bridge variance is the product of its distances from the endpoints.",
        H("Bernoulli Bridge Variance"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("bernoulli-bridge-variance-is-t-times-one-minus-t"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/Endpoints/BernoulliBridgeVariance.bernoulli_bridge_variance"),
                H("The Bernoulli bridge variance is t times one minus t"),
                StatementSource.FromAuthor(Disp(Seq(
                    UnitIntervalBinder(),
                    BridgeVariance(F.Id("t")), Sp, Eq, Sp,
                    F.Id("t"), Open, D(1), Sp, Minus, Sp, F.Id("t"), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The bridge at t is the Bernoulli probability measure placing mass t at one "
                        + "and mass one minus t at zero. The identity observable therefore has mean t.")),
                    Paragraph(Text(
                        "Mathlib states the corresponding binomial variance formula only as an "
                        + "unproved placeholder in this pinned revision. The Lean proof instead uses "
                        + "the proved Bernoulli integral formula and the definition of variance, then "
                        + "finishes by ring normalization.")),
                    Paragraph(Text(
                        "This closes only the exact bridge-variance identity. The source's numerical "
                        + "five-point fit and its broader interpretive comparisons remain unresolved."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bernoulli-bridge-variance-at-endpoints-and-midpoint"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/Endpoints/BernoulliBridgeVariance."
                    + "bernoulli_bridge_variance_endpoints_and_midpoint"),
                H("The bridge variance vanishes at the endpoints and is one quarter at the midpoint"),
                StatementSource.FromAuthor(Disp(Seq(
                    BridgeVariance(D(0)), Sp, Eq, Sp, D(0), Sp, Land, Sp,
                    BridgeVariance(D(1)), Sp, Eq, Sp, D(0), Sp, Land, Sp,
                    BridgeVariance(F.Seq(Frac, Grp(D(1)), Grp(D(2)))), Sp, Eq, Sp,
                    Frac, Grp(D(1)), Grp(D(4)), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Substitution in the exact variance identity gives both zero endpoint values "
                    + "and the displayed midpoint value without numerical approximation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bernoulli-bridge-variance-is-at-most-one-quarter"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/Endpoints/BernoulliBridgeVariance."
                    + "bernoulli_bridge_variance_le_quarter"),
                H("The bridge variance is at most one quarter"),
                StatementSource.FromAuthor(Disp(Seq(
                    UnitIntervalBinder(), BridgeVariance(F.Id("t")), Sp, Leq, Sp,
                    Frac, Grp(D(1)), Grp(D(4)), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Completing the square bounds t times one minus t by one quarter on the unit "
                    + "interval."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bernoulli-bridge-variance-reaches-one-quarter-only-at-midpoint"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/Endpoints/BernoulliBridgeVariance."
                    + "bernoulli_bridge_variance_eq_quarter_iff"),
                H("The bridge variance reaches one quarter exactly at the midpoint"),
                StatementSource.FromAuthor(Disp(Seq(
                    UnitIntervalBinder(), Open,
                    BridgeVariance(F.Id("t")), Sp, Eq, Sp, Frac, Grp(D(1)), Grp(D(4)),
                    Sp, Leftrightarrow, Sp,
                    F.Id("t"), Sp, Eq, Sp, Frac, Grp(D(1)), Grp(D(2)), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Equality in the completed-square bound forces t to equal one half, and direct "
                    + "substitution proves the converse."))),
                DescribeRole.Theorem)),
        []));
}
