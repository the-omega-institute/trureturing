using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9AdjacentHuangDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9AdjacentHuang";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adjacent Hamming cuts in the Huang action",
        H("Adjacent Hamming cuts in the Huang action"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-huang-cut-commutation"),
                DeclarationHandle.Create(Module + ".cutAction_commutes"),
                H("An adjacent cut commutes with the full action"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each signed coordinate flip changes the Hamming rank by one. The square of the weighted Huang operator is a scalar operator. Its off-diagonal blocks between ranks two apart therefore vanish, which gives commutation with the action on a single adjacent cut."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-huang-cut-eigenvector"),
                DeclarationHandle.Create(Module + ".cutAction_eigenvector"),
                H("A cut yields a vector on its two ranks"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The cut sends an eigenvector to a solution of the same eigenvalue equation supported on the two ranks of the cut."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-huang-cut-energy"),
                DeclarationHandle.Create(Module + ".cutAction_edge_energy"),
                H("The two rank energies count the induced edges"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For an integral coherent switching at unit weights and eigenvalue three, the cut vector has squared norm three times the induced cut edge count on each rank. Coherence counts each edge with positive contribution, and the signed action is self-adjoint."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-huang-odd-cut-parity"),
                DeclarationHandle.Create(Module + ".cutAction_odd_cut_even_edges"),
                H("An odd lower rank forces even cut size"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Sum the exterior rows below the lower rank modulo two. Each vertex of that rank is counted once per occupied coordinate, so odd rank forces its integral energy to be even. The energy formula then makes the cut edge count even.")),
                    Paragraph(Text("In the separated 120+138 case of Hong, Wu and Xia's Problem 2, translating the cube aligns the nine majority orientations of the 120-vertex component into one alternating class of Hamming cuts. Diagonal sign switching after translation preserves coherence and the unit-weight eigenvalue equation. If every axis has a 19+1 fold, the two classes have nine and 171 edges. The class that starts at odd ranks contradicts the even cut count. https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
                DescribeRole.Theorem)),
        []));
}
