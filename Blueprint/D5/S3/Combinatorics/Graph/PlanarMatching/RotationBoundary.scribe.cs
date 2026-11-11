using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PlanarMatching;

internal sealed class RotationBoundaryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PlanarMatching/RotationBoundary.";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/RibbonEmbeddings/cimasoni2007dimers");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact actual-dart facial boundaries and face-odd orientations of even-order signed-Euler-two rotations.",
        H("Actual facial boundaries and face-odd orientations"),
        Blocks(
            Paragraph(Text(
                "Let V be an arbitrary finite vertex type with decidable equality, and G a connected simple graph on V with decidable adjacency and at least one actual dart. "
                + "Rotation G consists of a permutation rho of G.Dart whose SameCycle classes are precisely the darts with a common first vertex. "
                + "Reversal alpha sends a dart to its symm. The facial successor phi first reverses a dart and then applies rho. "
                + "Face is the quotient by SameCycle phi, using integer powers and retaining every orbit, including singleton orbits. "
                + "The edge type E is G.edgeSet, the subtype of actual unordered edges. No side, surface realization or parity property is included in Rotation.")),
            Paragraph(Text(
                "The boundary linear map B takes a face function x with values in ZMod 2 to the edge function whose value is the sum of the two facial shore values. "
                + "Its definition chooses an actual representative dart of each unordered edge. Its evaluation theorem proves that the sum is independent of that choice. "
                + "Every cardinality in the Euler hypothesis is cast to the integers before subtraction: card(V) minus card(E) plus card(Face) equals two.")),
            Describe.Lean(DescribeId.Create("face-cycle-exact"),
                DeclarationHandle.Create(Prefix + "face_cycle_exact"),
                H("The face boundary map is exact onto the actual cycle space"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For every finite V, G and Rotation satisfying the stated connectedness, actual-dart nonemptiness and signed integer Euler equation, three conclusions hold together. "
                        + "For every face function x and actual dart d, B(x) on the unordered edge of d is x(face d) plus x(face alpha(d)). "
                        + "For every x, B(x) is zero if and only if there exists c in ZMod 2 such that x is the constant function with value c. "
                        + "The linear range of B equals SimpleGraphCycleSpace.simpleCycleSpace G, the existing span of indicators of actual simple cycles.")),
                    Paragraph(Text(
                        "Zero boundary equates opposite shore values. Facial succession then equates values after a rotor step, and an actual graph walk propagates this equality between all faces. "
                        + "Reindexing a dart sum along phi proves that every facial boundary annihilates the vertex-to-edge differential. "
                        + "The existing finite_graph_cycle_space theorem identifies these relations with the existing cycle space. "
                        + "Rank-nullity, the one-dimensional constant kernel and the signed Euler equation establish equality of the two subspaces. "
                        + "Generic cycle rank and linear algebra are reused; geometric separation is not assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("face-step"),
                DeclarationHandle.Create(Prefix + "face_step"),
                H("Facial succession preserves its actual face"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every actual dart d, face(facePerm d) equals face d, since Face is the complete SameCycle quotient of the actual facial successor."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("boundary-dart"),
                DeclarationHandle.Create(Prefix + "boundary_dart"),
                H("The boundary is independent of the chosen representative"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every actual dart d and every binary facial labelling x, boundary x on the unordered edge of d equals x(face d) plus x(face d.symm). The two representatives of an unordered edge differ at most by reversal."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("boundary-relation"),
                DeclarationHandle.Create(Prefix + "boundary_relation"),
                H("Every facial boundary annihilates the vertex differential"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For a finite vertex type with decidable graph adjacency, every facial labelling has boundary in BinaryCharacterCodeDuality.characterRelationSpace of the actual endpointCharacters G. Reindexing the complete dart sum by the facial successor cancels the endpoint contributions in ZMod 2."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("boundary-zero"),
                DeclarationHandle.Create(Prefix + "boundary_eq_zero_iff"),
                H("The facial boundary kernel consists of constants"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For a connected graph on a finite vertex type with decidable adjacency, boundary x is zero if and only if there exists c in ZMod 2 with x equal to the constant function c. The statement includes the case with no actual darts or faces and uses neither Euler nor geometric assumptions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sum-darts"),
                DeclarationHandle.Create(Prefix + "sum_darts"),
                H("Unordered edge pairs enumerate all actual darts"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every additive commutative monoid K and every f from actual darts to K, the sum over actual unordered edges of f on the chosen representative and on its reverse equals the sum of f over all actual darts. The vertex type is finite and adjacency decidable; no rotation hypothesis is needed."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exists-face-odd"),
                DeclarationHandle.Create(Prefix + "exists_face_odd"),
                H("Face-odd orientations exist for even vertex order"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every connected finite simple graph with decidable equality and adjacency, a nonempty actual dart type, a Rotation and signed integer Euler expression card(V) minus card(E) plus card(Face) equal to two, even card(V) implies existence of epsilon on actual darts with epsilon(d.symm) equal to one plus epsilon(d) and faceOpposition epsilon f equal to one for every complete face orbit. The proof solves the face defects through the dual of boundary, using the constant kernel and even total defect. This construction is consumed by the nice-cycle theorem in RotationFaces."))), DescribeRole.Theorem),
            Paragraph(Text("The faceOpposition definition counts every actual dart in its complete face orbit. The face-odd construction, facial kernel, dart evaluation and dart summation are used by the actual regional Euler and nice-cycle consumer in RotationFaces. These are finite combinatorial results; geometric realization, matching-sign transport, Pfaffian identities and complexity bounds remain separate obligations."))), []));
}
