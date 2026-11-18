using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Characters;

internal sealed class LatticeDiscriminantShiftedThetaDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Source-coupled discriminant theta inversion",
        H("Source transformation"), Blocks(
        Describe.Lean(DescribeId.Create("discriminant-shifted-shiftedtheta-real-s"),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/Characters/LatticeDiscriminantShiftedTheta.shiftedTheta_real_S"),
            H("Inversion with a real source"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Translated Poisson summation resolves the dual lattice into its finite discriminant sectors. The dual theta argument is minus the reciprocal period and the source is divided by the original period. The Fourier character uses the original unshifted frequency."))),
            DescribeRole.Theorem))));
}
