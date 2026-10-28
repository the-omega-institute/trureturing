using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Golay;

internal sealed class RealLeechDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Golay/RealLeech.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual Golay construction as a positive even unimodular real lattice", H("The actual Golay construction as a positive even unimodular real lattice"),
        Blocks(
            Node("claim-1", "lattice", "The exact real image of the original integer subgroup",
                "The lattice is the image under coordinate inclusion of IntegerLeech.integerLattice for the explicit GolayEncoder.code. The form is the real coordinate dot product divided by eight. The dot-over-eight form has the same normalization as the real coordinate dot product after coordinate division by the square root of eight.", DescribeRole.Definition),
            Node("claim-2", "mem_lattice", "Membership preserves the actual construction",
                "Every real member has an integer representative satisfying the original Admissible predicate, and every such representative lies in the image.", DescribeRole.Theorem),
            Node("claim-3", "even_norm", "Actual norms are even",
                "The existing squareSum_div_sixteen theorem supplies the even norm with no new divisibility assumption.", DescribeRole.Theorem),
            Node("claim-4", "integral_pairing", "The actual pairing is integral",
                "The existing pairing_integral theorem supplies an integer value for every pair of real image points.", DescribeRole.Theorem),
            Node("claim-5", "self_dual", "The actual real lattice is selfdual",
                "All binary hypotheses are discharged by the existing explicit Golay code. The exact original integer representation supplies raw membership, and its existing integral pairing theorem supplies the converse dual inclusion. No real selfduality, determinant, index or covolume is used as a premise.", DescribeRole.Theorem),
            Node("claim-6", "exists_positive_even_unimodular_gram", "Rank twenty-four integral charges preserve the full form",
                "The coordinate integer lattice contains the actual image discretely, while the actual eight-coordinate probes prove full real span. The native integer lattice basis gives LatticeData of rank twenty-four with positive definite even integral Gram matrix and unit determinant, together with a charge linear equivalence into the actual image preserving the full dot-over-eight pairing. This establishes lattice data only; the holomorphic VOA, Monster action, CFT and string or holographic realizations require further mathematical constructions.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
