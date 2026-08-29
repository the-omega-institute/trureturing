using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.WorldModel;

internal sealed class FixedPointStabilityProfileDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/WorldModel/FixedPointStabilityProfile.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform fixed-point stability is recorded by a worst-case multiplier radius.",
        H("Fixed-Point Stability Profiles"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-projective-profile-has-uniform-radius"),
                DeclarationHandle.Create(Prefix + "golden_constant_profile_uniform"),
                H("The canonical golden profile is uniformly attracting"),
                StatementSource.FromAuthor(GoldenRadiusFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "UniformRadiusBound separates the multiplier field from fixedness "
                            + "and bridge coherence. A valid radius is nonnegative, strictly "
                            + "below one, and bounds the absolute multiplier in every model.")),
                    Paragraph(Text(
                        "For the canonical golden projective profile, every multiplier is minus "
                            + "the inverse golden ratio squared. The exact uniform radius is its "
                            + "positive absolute value, varphi to the power minus two.")),
                    Paragraph(Text(
                        "The theorem is scoped to the specified golden projective family. It does "
                            + "not assert attraction under arbitrary self-maps."))),
                DescribeRole.Theorem))));

    private static Formula GoldenRadiusFormula() => Disp(Seq(
        Forall, Sp, F.Id("i"), Comma, Sp,
        Call("abs", Sub(F.Id("lambda"), F.Id("i"))), Sp, Eq, Sp,
        F.Id("varphi"), Caret, Grp(Minus, D(2)), Sp, Lt, Sp, D(1)));
}
