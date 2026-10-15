using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockTargetThetaChargedWeightDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original charged L0 supplier binding",
        H("Original charged L0 supplier binding"),
        Blocks(Describe.Lean(
            DescribeId.Create("latticehalffocktargetthetachargedweight-charged-tensor-L0-covariance"),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockTargetThetaChargedWeight.charged_tensor_L0_covariance"),
            H("Original charged L0 supplier binding"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Background),
            Blocks(Paragraph(Text("The exact completed source proof body is retained in this consumed module. Checked private aliases repair visibility without changing any protected predecessor. This is supplier reuse, not a second claim of new mathematics. Both inverse-Gram equations remain explicit whenever present. The full original goal and the independent spectral classification remain outside this statement."))),
            DescribeRole.Theorem))));
}
