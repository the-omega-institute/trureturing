using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.GolayLeech;

internal sealed class ExplicitLeechLatticeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/GolayLeech/ExplicitLeechLattice.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit Golay-congruence lattice mathematics.",
        H("Exact integral construction"),
        Blocks(
            Describe.Lean(DescribeId.Create("result-0"),
                DeclarationHandle.Create(Prefix + "charge_pairing_scaled"), H("Original lattice normalization"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original LatticeData bilinear pairing on arbitrary charges equals the coordinate dot product of B times the charges divided by eight. Every integer scaling identity is proved."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result-1"),
                DeclarationHandle.Create(Prefix + "real_positive"), H("Genuine positive definiteness"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The real extension of B is injective because its actual determinant is nonzero. The scaled Gram identity turns every nonzero real quadratic value into a positive sum of squares."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result-2"),
                DeclarationHandle.Create(Prefix + "actual_leech_supplier"), H("Explicit rank-24 supplier and original ground"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The concrete original LatticeData has rank twenty-four, determinant one, even norms, minimum nonzero norm four, attained norm four and the full congruence/basis identity. Its actual unit determinant is passed directly to actual_twisted_ground_representation, obtaining the original irreducible ground of dimension 4096. This does not construct the full moonshine extension, Monster action, a fusion category, string dynamics or AdS/CFT."))), DescribeRole.Theorem))));
}
