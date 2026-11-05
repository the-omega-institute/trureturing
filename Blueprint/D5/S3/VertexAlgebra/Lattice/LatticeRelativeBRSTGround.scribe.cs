using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;

internal sealed class LatticeRelativeBRSTGroundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/LatticeRelativeBRSTGround.";
    private static DocumentBlock Node(string name, string prose, DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create("latticerelativebrstcohomology-" + name.Replace(".", "-").Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]), H(name), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original relative-shell constraints and exact-energy ground target",
        H("Original relative-shell constraints and exact-energy ground target"), Blocks(
            Node("Ground.energyTarget", "The complex submodule of transverse polynomials whose nonzero coefficients have exact integer energy weight(nu)+chargeEnergy(D,p)=1. It is defined by coefficient vanishing outside that equality, independently of the shell, groundMap or P0.", DescribeRole.Definition))));
}
