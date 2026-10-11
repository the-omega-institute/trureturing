using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class CountedGroupOverlapDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/CountedGroupOverlap.";
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula U => F.Id("U");
    private static Formula V => F.Id("V");
    private static Formula UV => Call("product", U, V);
    private static Formula All(Formula body, params Formula.BoundVariable[] extra) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [B("H", F.Id("Type")), B("group", Call("Group", F.Id("H"))),
             B("finite", Call("Fintype", F.Id("H"))), B("n", F.Id("Nat")),
             B("m", F.Id("Nat")),
             B("U", Call("GroupMat", F.Id("H"), F.Id("n"), F.Id("m"))),
             B("V", Call("GroupMat", F.Id("H"), F.Id("m"), F.Id("n"))),
             .. extra], body);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Each total group label has its own finite path fiber. Splitting those fibers transports both numbered histories and their group coordinates.",
        H("Counted group-labelled overlap codes"),
        Blocks(
            Describe.Lean(DescribeId.Create("group-counted-split-join"),
                DeclarationHandle.Create(Prefix + "split_join"), H("Recover both labelled half-edges"),
                StatementSource.FromAuthor(Disp(All(Equal(
                    Call("split", U, V, Call("join", U, V, F.Id("a"), F.Id("b"), F.Id("h"))),
                    Call("pair", F.Id("a"), F.Id("b"))),
                    B("a", Call("Edge", U)), B("b", Call("Edge", V)),
                    B("h", Equal(Call("target", F.Id("a")), Call("source", F.Id("b"))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The total-label fiber equivalence retains the middle vertex, both labels and both parallel-edge numbers, so splitting after joining recovers the full pair."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("group-counted-join-split"),
                DeclarationHandle.Create(Prefix + "join_split"), H("Recover the original labelled edge"),
                StatementSource.FromAuthor(Disp(All(Equal(
                    Call("join", U, V, Call("first", Call("split", U, V, F.Id("a"))),
                        Call("second", Call("split", U, V, F.Id("a")))), F.Id("a")),
                    B("a", Call("Edge", UV))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The split half-edges have matching middle endpoints; their equality proof is implicit in the displayed join. The inverse total-label fiber equivalence recovers the original outside endpoints, total label and parallel-edge number."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("labelled-edge-coordinates"), DeclarationHandle.Create(Prefix + "edgeCoordinates"),
                H("Every actual edge coordinate"), StatementSource.FromAuthor(Disp(All(Call("Equiv", Call("Edge", F.Id("M")), Call("SigmaEdgeCoordinates", F.Id("M"))), B("M", Call("GroupMat", F.Id("H"), F.Id("n"), F.Id("m")))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("edgeCoordinates sends an edge to the dependent tuple of source, target, group label and copy number, and reconstructs those exact four fields. The number type is Fin(coeff(M[source,target],label)); empty coefficient fibers contribute no edge. edgeFintype enumerates this complete sigma type and edgeDecidableEq transports decidable coordinate equality. No parallel edges are identified."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("ordered-labelled-fiber"), DeclarationHandle.Create(Prefix + "orderedFiberEquiv"),
                H("The prescribed lexicographic rank"), StatementSource.FromAuthor(Disp(All(Call("Equiv", Call("Fin", Call("coeff", Call("entry", UV, F.Id("i"), F.Id("k")), F.Id("g"))), Call("Fiber", U, V, F.Id("i"), F.Id("k"), F.Id("g"))), B("order", Call("LinearOrder", F.Id("H"))), B("i", Call("Fin", F.Id("n"))), B("k", Call("Fin", F.Id("n"))), B("g", F.Id("H"))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For fixed outside endpoints i,k and total label g, rank the dependent fiber by intermediate j, first label alpha in the supplied total order, first copy cU, then second copy cV. The second label is alpha inverse times g. The nested sigma and product orders are lexicographic. The cardinality is reused from fiberEquiv, but the map is the pinned increasing orderIsoFinOfCardEq, not its arbitrary enumeration. Empty fibers are included with cardinality zero. This is a consumed rank adapter, not a novel conjugacy theorem."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("orderedsplit"), DeclarationHandle.Create(Prefix + "orderedSplit"),
                H("orderedSplit"), StatementSource.FromAuthor(Disp(All(Call("Prod",Call("Edge",U),Call("Edge",V)), B("order",Call("LinearOrder",F.Id("H"))), B("a",Call("Edge",UV))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("orderedSplit reads the original total-label numbered edge through orderedFiberEquiv and returns the actual two half-edges. It retains both outside endpoints, the shared middle vertex, first label alpha, second label alpha inverse times the original label, and both copy numbers."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("orderedjoin"), DeclarationHandle.Create(Prefix + "orderedJoin"),
                H("orderedJoin"), StatementSource.FromAuthor(Disp(All(Call("Edge",UV), B("order",Call("LinearOrder",F.Id("H"))), B("a",Call("Edge",U)), B("b",Call("Edge",V)), B("h",Equal(Call("target",F.Id("a")),Call("source",F.Id("b"))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("orderedJoin uses the inverse prescribed fiber rank on two actual composable half-edges. Its label is the ordered product of the first and second labels. Its endpoints and number are those of this same ordered rank."))), DescribeRole.Definition))));
}
