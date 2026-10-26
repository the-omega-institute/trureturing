using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Golay;

internal sealed class GolayOctadCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Golay/GolayOctadCount.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuadraticForms/nebe2014leechcatalogue");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Second moments and Golay octads",
        H("Second moments and Golay octads"),
        Blocks(
            Paragraph(Text("Pair projections and the second Hamming-weight moment determine the octad count without a list of code messages. The parameterized argument varies the binary linear code. Fiber counting and moment identities are classical methods; no originality claim is made.")),
            Node("golayoctadcount-pair-projection", "pairProjection", "Two-coordinate additive projection",
                "For a binary linear subspace C and coordinates i and j, pairProjection is the additive map sending a codeword c to its actual coordinate pair (c_i,c_j).", DescribeRole.Definition, false),
            Node("golayoctadcount-pair-projection-surjective", "pairProjection_surjective", "Surjectivity at distinct coordinates",
                "For any binary linear subspace C containing the all-ones word, equal to its coordinate-pairing orthogonal, and having minimum nonzero weight at least eight, the actual projection to any two distinct coordinates is surjective onto F2 times F2. Failure to separate the coordinates would put their weight-two indicator in C, contradicting the minimum-weight assumption. This exposed original helper supplies the Leech axis distribution.", DescribeRole.Theorem, false),
            Node("golayoctadcount-pair-fiber-card", "pair_fiber_card", "Size of the two-one fiber",
                "Under those same structural hypotheses and cardinality 4096, exactly 1024 codewords have value one at both distinct coordinates. Translation identifies all four fibers. The axis distribution consumes this original fiber count and projection surjectivity to count every bit pair.", DescribeRole.Theorem, false),
            Node("golayoctadcount-octad-count-of-self-dual", "octad_count_of_self_dual", "Octads from structural hypotheses",
                "For any binary linear subspace C on twenty-four coordinates, assume cardinality 4096, membership of the all-ones word, equality to its coordinate-pairing orthogonal, minimum nonzero weight at least eight, and weight spectrum contained in zero, eight, twelve, sixteen and twenty-four. The subtype of weight-eight words then has cardinality 759. Self-duality and minimum weight force every two-coordinate projection to be surjective. Its four fibers each have 1024 elements, giving second moment 565248. Complementation equates the weight-eight and weight-sixteen counts. The size and moment equations force 759.", DescribeRole.Theorem, false),
            Node("golayoctadcount-octad-card", "octad_card", "Octads of the actual polynomial code",
                "The weight-eight subtype of the original polynomial encoder image has cardinality 759. The established code cardinality, all-ones membership, self-duality, minimum weight and weight spectrum supply every hypothesis of the structural theorem. This is the classical Golay octad count.", DescribeRole.Theorem, true))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role, bool attested) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(),
            attested ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
