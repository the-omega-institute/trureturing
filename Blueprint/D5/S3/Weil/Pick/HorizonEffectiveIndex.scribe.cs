using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Pick;

internal sealed class HorizonEffectiveIndexDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Weil/Pick/HorizonEffectiveIndex.finite_hankel_horizon_effective_index";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Effective Hankel defect indices obey positivity, product, sum, and boundary laws.",
        H("Horizon Effective Index"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-hankel-horizon-effective-index"),
                DeclarationHandle.Create(Declaration),
                H("Finite Hankel horizon effective index"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Finite square real matrices model the finite-rank Hankel operators. "
                            + "Strict contraction is stated by requiring every spectrally "
                            + "defined singular value to be below one.")),
                    Paragraph(Text(
                        "The characteristic polynomial of the Hermitian Gram matrix, evaluated "
                            + "at one, gives the singular-value product for the defect "
                            + "determinant. Positivity makes the defect invertible and proves the "
                            + "reciprocal determinant and logarithmic formulas.")),
                    Paragraph(Text(
                        "Block determinants give orthogonal-sum multiplicativity, the zero "
                            + "matrix gives normalization and an explicit inhabited Hankel "
                            + "example, and the reciprocal singular factor tends to infinity at "
                            + "the contractive boundary.")),
                    Paragraph(Text(
                        "The declaration formalizes only the effective information index. It "
                            + "does not claim that a Jones index has been constructed."))),
                DescribeRole.Theorem))));
}
