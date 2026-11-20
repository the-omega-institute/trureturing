using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction;

internal sealed class SevenSiteLineEvaluationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteLineEvaluation";
    private const string Title = "Affine restriction and first derivatives of the seven-site observation";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("sevensitelineevaluation-natdegree-affinerestriction-le"),
                DeclarationHandle.Create(Module + ".natDegree_affineRestriction_le"),
                H("Degree of the affine restriction"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any polynomial in the five slice coordinates over a commutative ring, substitution of the specified affine line gives a univariate polynomial whose natural degree is at most the original total degree."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sevensitelineevaluation-eval-partial"),
                DeclarationHandle.Create(Module + ".eval_partial"),
                H("First partial at a slice point"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any slice point and Pauli observation entry over a commutative ring, evaluation of the formal partial equals the corresponding square-zero coefficient of the observation. The coordinate direction supplies the square-zero input."))),
                DescribeRole.Theorem))));
}
