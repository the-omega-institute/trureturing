using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves;

internal sealed class Q9BinaryAxialCompletionDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9BinaryAxialCompletion";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A binary adjacency equation determines axial completions of the weight-32 residual.",
        H("Binary adjacency determines axial completions"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("binary-completion-iff"),
                DeclarationHandle.Create(Module + ".binary_completion_iff"),
                H("Axial completion is equivalent to the binary neighbor equations"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Each bit chooses the layer of an odd singleton. In each even row their unsigned sum must equal the indicator of the even residual modulo two.")),
                    Paragraph(Text("After switching the odd word by these bits, the same row condition is a congruence modulo four for its signed image. The transverse row bound restricts those image values to zero or four in absolute value outside the even singleton support, and to two on that support. The squared Huang operator supplies the complementary layer equations."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("binary-dimer-geometry"),
                DeclarationHandle.Create(Module + ".binary_dimer_geometry"),
                H("Every dimer site has even parity and four odd singleton neighbors"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For a solution of the binary equations with singleton energies 16 and 32, binary_dimer_count shows that twelve rows have absolute value four. Its proof uses the squared norm 256 and subtracts the contribution 64 from the even singletons. The geometry theorem gives even parity, exclusion from the singleton support, and four odd neighbors at every such row.")),
                    Paragraph(Text("This describes the weight-32 residual in one 72-vertex case of Hong–Wu–Xia, Section 7, Problem 2. https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("completion-graph"),
                DeclarationHandle.Create(Module + ".completion_graph"),
                H("The raw signed layers induce a cubic switched subgraph on 72 vertices"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The occupied directions enumerate the actual neighbors in the induced graph. The transverse signs and axial equality give the switching identity on each occupied edge. The two disjoint layer images have total cardinality 72."))),
                DescribeRole.Theorem)),
        []));
}
