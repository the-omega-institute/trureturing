using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class DyadicSmoothingIdentitiesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/DyadicSmoothingIdentities.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dyadic block identity.",
        H("Identities for dyadic smoothing"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("smoothing-block-eq-averaged-increments"),
                DeclarationHandle.Create(Prefix + "smoothingBlock_eq_averaged_increments"),
                H("Dyadic block identity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For R>0, Z_R=A_R(A_R E) and B_R=Z_R-Z_(2R) satisfy B_R=-A_R(A_R D_R E)/2-A_R(A_R D_(2R) E)/4 pointwise. Splitting each window of length 2R into two windows of length R yields this identity."))),
                DescribeRole.Theorem))));
}
