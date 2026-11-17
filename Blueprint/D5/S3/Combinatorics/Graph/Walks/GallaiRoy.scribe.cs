using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class GallaiRoyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Walks/GallaiRoy.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/traversogianini2026brooks");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite simple graph is k-colorable exactly when an orientation bounds every injective directed path by k vertices.",
        H("The Gallai–Hasse–Roy–Vitaver theorem"),
        Blocks(
            Paragraph(Text("Let V be any finite type in any universe, G a simple undirected graph on V, and k a natural number. Colorable(G,k) means that a proper vertex coloring with values in Fin(k) exists; colors may be unused. No chosen enumeration, decidable adjacency, nonempty vertex set, positive k, connectedness or acyclicity of the input orientation is required. Relations(V) denotes V to V to Prop, and Functions(A,B) denotes the functions from A to B.")),
            Describe.Lean(DescribeId.Create("orientation"), DeclarationHandle.Create(Prefix + "IsOrientation"),
                H("Orientation convention"), StatementSource.FromAuthor(OrientationFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Every undirected edge must have at least one arc direction, and every arc must be an edge. Both directions on one edge are allowed. Since G has no loops, an orientation has no loops. The word orientation here does not require exactly one direction."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("directed-path"), DeclarationHandle.Create(Prefix + "IsDirectedPath"),
                H("Paths count vertices"), StatementSource.FromAuthor(PathFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For any natural m, a path is an injective function f from Fin(m) to V such that an arc joins f(i) to f(i+1) whenever i+1 is less than m. The displayed natural indices carry their canonical Fin(m) bounds. The path has m vertices and, when m is positive, m-1 edges. The empty function is a path with zero vertices; every singleton function is a path with one vertex. Neither a closing arc nor a terminal-to-initial equality is imposed."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("coloring-equivalence"), DeclarationHandle.Create(Prefix + "colorable_iff_exists_orientation"),
                H("Colorings and bounded-path orientations"), StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For all V, G and k as above, G is k-colorable if and only if there exists a relation o satisfying the orientation convention and bounding every injective directed path by k vertices. The path bound quantifies over every natural m and every f from Fin(m) to V, rather than only paths presented by a selected walk representation.")),
                    Paragraph(Text("From a coloring c, orient each edge from its smaller color to its larger color. Properness supplies a direction on every edge. Along a directed path the colors strictly increase, so their composite with f is an injection into Fin(k), giving m at most k.")),
                    Paragraph(Text("For the converse choose, among all acyclic subrelations D of o, one maximal under inclusion. Such a relation exists because V is finite and the empty relation is acyclic. Every D-chain is without repetition: a repeated vertex would yield a nonempty D-path back to itself. Thus its underlying list gives an injective o-path, and the assumed bound limits its number of vertices.")),
                    Paragraph(Text("For each vertex v let h(v) be the largest number of edges in a D-chain starting at v. The singleton chain exists, and the path bound gives h(v) less than k. Every nonempty D-path from a to b lets one prepend that path to a longest chain from b, so h(b) is strictly less than h(a). If an original arc u to v is absent from D, maximality forces a D-path from v back to u: otherwise adding that arc preserves acyclicity and strictly enlarges D. The added-edge path decomposition verifies this assertion even when a walk traverses the new arc more than once. The endpoints differ because o has no loops, so this return path is nonempty. Their heights again differ. Consequently every original graph edge has unequal endpoint heights, and v mapped to h(v) in Fin(k) is a proper coloring.")),
                    Paragraph(Text("Empty V is included for every k, including zero: its empty coloring and empty relation satisfy the statement. For nonempty V, the singleton directed paths force k at least one, so neither side holds at k=0. Reciprocal arcs and directed cycles in o remain within the theorem; acyclicity belongs only to the selected internal subrelation D. The reverse construction happens to produce an acyclic orientation, but the existential statement does not impose that extra condition."))), DescribeRole.Theorem),
            Paragraph(Text("This is the classical Gallai–Hasse–Roy–Vitaver theorem. Roy's Theorem 1 and the sharpness discussion supply the historical mathematical reference. The Lean construction is received from Juan Pablo Traverso Gianini's immutable Lean Pool source; its maximal-acyclic argument is not attributed as Roy's original proof. The source note records exact software attribution and licenses, and identifies the related restricted native-rank application. Roy's stronger Theorem 2 is outside this statement.")))));

    private static Formula OrientationFormula()
    {
        Formula v = F.Id("V"), g = F.Id("G"), o = F.Id("o"), a = F.Id("a"), b = F.Id("b");
        return Disp(All("V", Call("Type"), All("G", Call("SimpleGraph", v), All("o", Call("Relations", v),
            Iff(Call("IsOrientation", g, o), And(
                All("a", v, All("b", v, Imp(Call("Adj", g, a, b), Or(Call("o", a, b), Call("o", b, a))))),
                All("a", v, All("b", v, Imp(Call("o", a, b), Call("Adj", g, a, b))))))))));
    }

    private static Formula PathFormula()
    {
        Formula v = F.Id("V"), o = F.Id("o"), m = F.Id("m"), f = F.Id("f"), i = F.Id("i");
        Formula next = new Formula.Binary(i, FormulaBinaryOperator.Add, D(1));
        Formula step = All("i", Call("Nat"), Imp(new Formula.Relation(next, FormulaRelationOperator.LessThan, m),
            Call("o", Call("f", i), Call("f", next))));
        return Disp(All("V", Call("Type"), All("o", Call("Relations", v), All("m", Call("Nat"),
            All("f", Call("Functions", Call("Fin", m), v), Iff(Call("IsDirectedPath", o, f), And(Call("Injective", f), step)))))));
    }

    private static Formula TheoremFormula()
    {
        Formula v = F.Id("V"), g = F.Id("G"), k = F.Id("k"), o = F.Id("o"), m = F.Id("m"), f = F.Id("f");
        Formula bound = All("m", Call("Nat"), All("f", Call("Functions", Call("Fin", m), v),
            Imp(Call("IsDirectedPath", o, f), new Formula.Relation(m, FormulaRelationOperator.LessThanOrEqual, k))));
        return Disp(All("V", Call("Type"), Imp(Call("Finite", v), All("G", Call("SimpleGraph", v),
            All("k", Call("Nat"), Iff(Call("Colorable", g, k), Ex("o", Call("Relations", v),
                And(Call("IsOrientation", g, o), bound))))))));
    }

    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Ex(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
}
