using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer.Constructor;

internal sealed class NativePositiveImageCoverDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositiveImageCover.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Residual occurrences in a total most-general free-term substitution",
        H("All named outputs and their comparison graph"), Blocks(
            Paragraph(Text("A presentation enumerates the entire finite family X of declared names, including unused names. C is any finite list of equations of free ordered binary terms with two distinct primitive labels. S is the actual successful result of the existing unifier from the empty substitution. Its total action assigns a term to every declared name. An unbound name is retained as its own variable. Interpreted native powers do not occur in this free-term problem. ListMem in the display denotes ordinary list membership, and sort is the third coordinate of an occurrence.")),
            Entry("Occurrence", "Residual positions retain their owners",
                "An occurrence is a triple (x,p,y): the declared output name x, an ordered Boolean address p, and the residual sort y. IsOccurrence means that the subtree of the total output at x and p is exactly the variable y. The finite list occurrenceVertices enumerates every such position in every declared output; it does not restrict to names visible in the input equations."),
            Entry("occurrenceEdges", "Edges come from every positive comparison",
                "decorate gives each residual position its own occurrence label, consistently whenever a declared name is reused. comparisonTerm substitutes these decorated total outputs into each side of a supplied equation. comparisonEdges descends through corresponding constructors and records corresponding residual leaves. occurrenceEdges concatenates these finite lists over all equations, retaining their order and repetitions. Connected is the equivalence closure of this edge relation, so edges may be traversed in either direction."),
            Describe.Lean(DescribeId.Create("total-mgu-residual-occurrence-graph"),
                DeclarationHandle.Create(Prefix + "mgu_occurrence_graph_exact"),
                H("Exact finite vertices, valid edges and residual-sort components"),
                StatementSource.FromAuthor(Disp(GraphExact())), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every presentation, every finite equation list and every actual successful unifier result, the computed vertex list contains exactly the residual occurrences of the total action. Every computed edge joins two valid vertices of the same residual sort. Among valid vertices, connectivity is equivalent to equality of their residual sorts. Thus each occurring residual sort has exactly one connected component. There is no connectedness assertion for an empty residual sort. An unused original name contributes its own isolated residual occurrence.")),
                    Paragraph(Text("To prove the nontrivial direction, color the component of one occurrence by one primitive ground leaf and all other components by the other primitive ground leaf. Evaluate each decorated output with these colors. Corresponding residual positions on every positive comparison are joined by an edge, so this modified total assignment still solves all equations. The existing most-generality restriction identity forces that assignment to factor through the actual total action. At each occurrence, its color must therefore be the value of its residual sort. Two occurrences of the same sort have equal colors and hence belong to the same component. Structural traversal supplies the exact vertex and edge correspondence.")),
                    Paragraph(Text("This theorem concerns the free-shape stage of native positive equation elimination. It supplies no interpreted constructor/collapse reduction, rank offsets, minimum bases, executable positive image charts or full-tuple native reconstruction. Those require additional arguments; free unification is not applied directly to interpreted native equations."))), DescribeRole.Theorem)
        )));

    private static DocumentBlock Entry(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("mgu-occurrence-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula GraphExact()
    {
        var s = Call("action", V("p"), V("S"));
        var vertices = Call("occurrenceVertices", V("p"), s);
        var edges = Call("occurrenceEdges", V("C"), s);
        Formula Member(Formula o) => Call("ListMem", o, vertices);
        Formula SameSort() => EqOf(Call("sort", V("a")), Call("sort", V("b")));
        var vertexLaw = All("o", Call("Occurrence", V("X")),
            IffOf(Member(V("o")), Call("IsOccurrence", s, V("o"))));
        var edgeLaw = All("a", Call("Occurrence", V("X")), All("b", Call("Occurrence", V("X")),
            Imp(Call("ListMem", Call("pair", V("a"), V("b")), edges),
                And(Member(V("a")), And(Member(V("b")), SameSort())))));
        var componentLaw = All("a", Call("Occurrence", V("X")), All("b", Call("Occurrence", V("X")),
            Imp(Member(V("a")), Imp(Member(V("b")),
                IffOf(Call("Connected", V("C"), s, V("a"), V("b")), SameSort())))));
        return All("X", V("Type"), All("p", Call("Presentation", V("X")),
            All("C", Call("Equations", V("X")), All("S", V("SubstInfo"),
                Imp(EqOf(Call("unify", Call("encodeEquations", V("p"), V("C")), V("empty")), Call("ok", V("S"))),
                    And(vertexLaw, And(edgeLaw, componentLaw)))))));
    }
    private static Formula V(string n) => F.Id(n);
    private static Formula Call(string n, params Formula[] args) => new Formula.Apply(Seq(Operatorname, Grp(V(n))), [.. args]);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Open, a, Sp, Land, Sp, b, Close);
    private static Formula Imp(Formula a, Formula b) => Seq(Open, a, Sp, Implies, Sp, b, Close);
    private static Formula IffOf(Formula a, Formula b) => Seq(Open, a, Sp, Iff, Sp, b, Close);
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, Open, b, Close);
}
