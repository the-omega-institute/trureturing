using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.GangulyCircuitAccess;

internal sealed class GangulyCombinatorialDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGeometry/ganguly2026stabilizersecretsharing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An exact binary certificate gives a nonempty pairwise intersecting circuit family and a proper dealer image for a member of that family.",
        H("Circuit access and dealer labels for the seven-vertex graph"),
        Blocks(
            Node("combinatorial-bits", "Bits", "Binary configurations",
                StatementSource.WithoutFormula(), DescribeRole.Definition,
                "Bits(n) is the type of functions from Fin(n) to the field ZMod(2). Vertices are numbered from zero."),
            Node("combinatorial-circuitauthorized", "circuitAuthorized", "Circuit-induced authorization",
                StatementSource.WithoutFormula(), DescribeRole.Definition,
                "A is circuit-authorized when d is outside A and some dealer circuit has its unsigned player support contained in A. Binary column relations in [I | M] have coefficient pairs (Mx, x). A circuit is a minimal nonempty relation support with at most one signed column per vertex. The player support forgets the signs and omits the dealer."),
            Node("combinatorial-quantumaccess", "quantumAccess", "Quantum access antecedent",
                StatementSource.WithoutFormula(), DescribeRole.Definition,
                "At least one player set is circuit-authorized, and every two circuit-authorized sets have nonempty intersection, including when the sets are equal. Upward closure is built into circuit authorization."),
            Node("combinatorial-dealerimage", "dealerImage", "Attainable dealer labels",
                StatementSource.WithoutFormula(), DescribeRole.Definition,
                "Take the set of pairs (x(d), (Mx)(d)) as x ranges over binary configurations for which both x and Mx vanish outside A together with d."),
            Node("combinatorial-witnessgraph", "witnessGraph", "The simple witness graph",
                StatementSource.WithoutFormula(), DescribeRole.Definition,
                "The vertex set is Fin(7). The unordered edges are 01, 02, 04, 06, 12, 13, 16, 23, 25, 45, 46 and 56."),
            Node("combinatorial-witnessdealer", "witnessDealer", "The dealer",
                StatementSource.WithoutFormula(), DescribeRole.Definition,
                "The dealer is vertex 4."),
            Node("combinatorial-witnessplayers", "witnessPlayers", "The retained players",
                StatementSource.WithoutFormula(), DescribeRole.Definition,
                "The retained set A consists of vertices 2, 5 and 6."),
            Node("combinatorial-witnessmatrix", "witnessMatrix", "Binary adjacency matrix",
                StatementSource.WithoutFormula(), DescribeRole.Definition,
                "The matrix M is the adjacency matrix of the witness graph over ZMod(2)."),
            Node("combinatorial-witness-authorized", "witness_authorized", "Circuit authorization for the retained players",
                StatementSource.WithoutFormula(), DescribeRole.Theorem,
                "The relation vector with a single one at vertex 5 gives the signed circuit {2, 4, 5*, 6}. Its minimality is checked against all 128 binary relation vectors. Its player support is A."),
            Node("combinatorial-witness-dealer-image", "witness_dealer_image", "A proper dealer image",
                StatementSource.WithoutFormula(), DescribeRole.Theorem,
                "The image on the retained set is exactly {(0, 0), (0, 1)}. Setting x(0), x(1) and x(3) to zero and requiring the same rows of Mx to vanish leaves x(5) free and forces x(2), x(4) and x(6) to zero."),
            Node("combinatorial-witness-quantum-access", "witness_quantum_access", "Quantum access for the circuit family",
                StatementSource.WithoutFormula(), DescribeRole.Theorem,
                "The witness matrix and dealer satisfy the quantum access antecedent. Every admissible nonempty dealer relation contains one of the ten listed supports 026, 036, 056, 236, 256, 356, 0123, 0125, 0135 and 1235. Each pair of these supports intersects. A common vertex of the two generator supports also belongs to both authorized supersets."),
            Node("combinatorial-discarded", "discarded", "Discarded players",
                StatementSource.WithoutFormula(), DescribeRole.Definition,
                "Remove the dealer and all retained vertices from Fin(n). For the witness the discarded vertices are {0, 1, 3}."),
            Node("combinatorial-config", "Config", "Configuration on a player register",
                StatementSource.WithoutFormula(), DescribeRole.Definition,
                "A configuration on a vertex set assigns an element of Fin(2) to each vertex in that set."),
            Node("combinatorial-fullconfig", "fullConfig", "Joint configuration with dealer",
                StatementSource.WithoutFormula(), DescribeRole.Definition,
                "For a discarded and retained configuration pair and a dealer bit s, use s at d, the retained coordinate at vertices of A other than d, and the discarded coordinate at every remaining vertex."),
            Node("combinatorial-graphphase", "graphPhase", "Quadratic graph phase",
                StatementSource.WithoutFormula(), DescribeRole.Definition,
                "For a matrix M and bit string z, sum M(i,j) z(i) z(j) over i < j in ZMod(2)."),
            Node("combinatorial-signedgraphentry", "signedGraphEntry", "Integer graph sign",
                StatementSource.WithoutFormula(), DescribeRole.Definition,
                "Raise minus one to the natural representative zero or one of the quadratic graph phase."),
            Node("combinatorial-witness-signed-cross-zero", "witness_signed_cross_zero", "Vanishing mixed-column sums",
                StatementSource.WithoutFormula(), DescribeRole.Theorem,
                "For every two retained configurations a and b, sum the product of the integer graph signs at (c,a,0) and (c,b,1) over all discarded configurations c. Each of the 64 sums, with eight terms each, equals zero."),
            Node("combinatorial-witness-signed-gram", "witness_signed_gram", "The integer Gram matrix",
                StatementSource.WithoutFormula(), DescribeRole.Theorem,
                "For each pair of dealer bits s and t, sum the product of their two signs over all pairs of discarded and retained configurations. The sum is 64 when s = t and zero otherwise."),
            Node("combinatorial-witness-dealer-surjective", "witness_dealer_surjective", "All labels on the dealer before restricting support",
                StatementSource.WithoutFormula(), DescribeRole.Theorem,
                "The map from all binary configurations to their dealer pair (x(4), (Mx)(4)) is surjective."))));

    private static DocumentBlock Node(string id, string name, string title, StatementSource statement,
        DescribeRole role, string prose) => Describe.Lean(
        DescribeId.Create("ganguly-circuit-access-" + id), DeclarationHandle.Create(Prefix + name),
        H(title), statement, AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);
}
