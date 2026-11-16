using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Characters;

internal sealed class LatticeDiscriminantWeilUnitaryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Characters/LatticeDiscriminantWeilUnitary.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hermitian unitarity of the finite discriminant Weil operators.",
        H("Finite Discriminant Weil Unitarity"),
        Blocks(
            Theorem("weil-s-preserves-inner", "weilS_preserves_inner", "Negative Weil Fourier unitarity",
                "The normalized negative discriminant Fourier operator preserves the standard finite Hermitian inner product on complex-valued discriminant functions."),
            Theorem("weil-t-preserves-inner", "weilT_preserves_inner", "Quadratic phase unitarity",
                "The quadratic half-norm multiplier preserves the same Hermitian inner product because its phase factors have unit norm."),
            Theorem("weil-st-preserves-inner", "weilST_preserves_inner", "Modular generator unitarity",
                "The composite Weil S followed by T preserves the finite Hermitian inner product, supplying the unitary modular-data interface for the lattice sectors."))));

    private static DocumentBlock Theorem(string id, string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
