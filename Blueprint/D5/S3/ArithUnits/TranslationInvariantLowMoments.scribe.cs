using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithUnits;

internal sealed class TranslationInvariantLowMomentsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ArithUnits/TranslationInvariantLowMoments.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite translation orbit forces low power moments to vanish in positive characteristic.",
        H("Translation-Invariant Low Moments"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("power-sum-eq-zero-of-add-invariant"),
                DeclarationHandle.Create(Prefix + "power_sum_eq_zero_of_add_invariant"),
                H("Low moments vanish under nonzero translation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For any finite subset of a field of prime characteristic preserved by "
                        + "a nonzero translation, power moments of degrees k with k + 1 below "
                        + "the characteristic vanish. Binomial expansion makes the translation "
                        + "action triangular on moments; induction cancels the nonzero diagonal "
                        + "coefficients. The boundary degree can have a nonzero moment, and the "
                        + "result alone does not imply a root-polynomial factorization."))),
                DescribeRole.Theorem))));
}
