using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Domination;

internal sealed class TotalDominationSeedsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Total-domination seed roots approach minus one from the right in actual finite graphs.",
        H("Right-hand total-domination seed roots"), Blocks(
            Paragraph(Text("A total dominating set S is an actual finite subset of the graph vertices. Every vertex v, including every selected vertex, must have a neighbour u in S. No independence, minimality, ordinary closed-neighbourhood domination, or connectedness restriction on S is substituted. The polynomial coefficients count exactly these subsets.")),
            Node("IsTotal", "Total domination", All("v", Call("V"), Some("u", Call("V"),
                And(Member(V("u"), V("S")), Call("Adj", V("G"), V("v"), V("u"))))),
                "For every actual graph G : SimpleGraph V and S : Finset V, IsTotal G S is the displayed proposition. V is implicit and has universe Type. The relation is the existing symmetric, loopless SimpleGraph adjacency.", DescribeRole.Definition),
            Node("totalPolynomial", "The actual subset polynomial", Eq(Call("totalPolynomial", V("G")),
                Call("sumTotalSubsets", V("G"))),
                "For every finite V with a Fintype instance and every SimpleGraph G on V, totalPolynomial G lies in the real polynomial ring. sumTotalSubsets denotes the sum over all S : Finset V of X raised to S.card when IsTotal G S holds, and zero otherwise. There is no supplied polynomial hypothesis.", DescribeRole.Definition),
            Node("unionGraph", "Disjoint union", Eq(Call("unionGraph", V("G"), V("H")), Call("disjointUnion", V("G"), V("H"))),
                "G : SimpleGraph V and H : SimpleGraph W give a graph on V sum W. Two left vertices use G adjacency, two right vertices use H adjacency, and vertices on opposite sides are not adjacent. The private subset equivalence union_total and sum bijection union_polynomial prove multiplicativity.", DescribeRole.Definition),
            Node("coneGraph", "A genuine universal vertex", Eq(Call("coneGraph", V("G")), Call("cone", V("G"))),
                "The vertex type is Unit sum V. The sole left vertex is adjacent to every right vertex; two right vertices use G adjacency; no left-left adjacency is allowed. For nonempty finite V, splitting subsets by hub membership proves T_cone(x)=x((1+x)^card(V)-1)+T_G(x). The selected hub itself requires a selected old vertex, which explains the subtraction of one.", DescribeRole.Definition),
            Node("SeedBase", "The seed vertex types", Eq(Call("SeedBase", V("m")), Call("recursiveSeedVertices", V("m"))),
                "m is any natural number. SeedBase 0 is Fin 3. SeedBase (m+1) is Fin 5 sum SeedBase m. Its exact cardinality is 5m+3. The explicit recursive Fintype instance supplies finite actual vertices at every unbounded order; the triangle supplies nonemptiness.", DescribeRole.Definition),
            Node("seedBaseGraph", "Five-cycles and a triangle", Eq(Call("seedBaseGraph", V("m")), Call("cycleTriangleUnion", V("m"))),
                "At m=0 this is the complete graph on Fin 3; at m+1 it is the disjoint union of the native cycleGraph 5 and seedBaseGraph m. Exact actual-subset enumeration gives T_C5=5x^3+5x^4+x^5 and T_K3=3x^2+x^3. Multiplicativity then gives their product for all m. These finite checks are consumed known ingredients of the unbounded seed estimate, not separate positive-instance results.", DescribeRole.Definition),
            Node("seedGraph", "The actual seed graph", Eq(Call("seedGraph", V("m")), Call("coneGraph", Call("seedBaseGraph", V("m")))),
                "For every natural m, the result is a simple graph on Unit sum SeedBase m. It has 5m+4 vertices. The universal vertex and nonempty base give every vertex a neighbour.", DescribeRole.Definition),
            Node("seedPolynomial", "The explicit seed polynomial", Eq(Call("seedPolynomial", V("m")), Call("seedExpression", V("m"))),
                "seedExpression(m) means x((1+x)^(5m+3)-1)+(5x^3+5x^4+x^5)^m(3x^2+x^3) in R[X]. The private theorem seed_graph_polynomial identifies this expression with the actual subset totalPolynomial(seedGraph m); it is not an abstract replacement for that polynomial.", DescribeRole.Definition),
            Node("seed_root_right", "A root in every shrinking interval", SeedRoot(false),
                "For every natural s>=3 with Odd s, there is a real r strictly between -1 and -1+1/s at which seedPolynomial(s^2) vanishes. Write t=1/s, a=(1-t)^3(1+3t+t^2), and g=2-3t+t^3. The bounds 0<=a<=1-3t^2 and s^2*3t^2=3 imply a^(s^2)<=1/4 by Bernoulli, since a(1+3t^2)<=1. Also 0<=g<=2 and t^(5s^2+3)<=1/27. The hub term is at least 52/81 and the subtracted term at most 1/2, so the right endpoint value is positive. Oddness gives the left endpoint value -1. Continuity and the strict intermediate value theorem produce the root.", DescribeRole.Theorem),
            Node("actual_seed_root_right", "The same roots belong to genuine isolate-free graphs", SeedRoot(true),
                "The same s and interval witness r satisfy totalPolynomial(seedGraph(s^2)).IsRoot r, that actual polynomial is nonzero, and every actual vertex has a neighbour. Nonzeroness follows from its value -1 at -1. Thus selected vertices obey the total condition in a real graph; no zero polynomial or density hypothesis supplies the conclusion. The underlying graph has 5s^2+4 vertices. This theorem is one auxiliary step toward Shao-Zhao arXiv:2609.06569v5 section 5.2 Open Problem 2, registered as issue 23313. It does not prove roots dense in C: independent-fibre substitution, large negative seeds, complex radial/angular approximation and the final Fin n witness assembly remain outside these statements.", DescribeRole.Theorem),
            Paragraph(Text("The cycle, triangle, cone and disjoint-union identities are attributed ingredients: arXiv:1605.02222 and the H-join framework of Subramanian and Selvakumar, Filomat 2025. No worldwide priority or independent admission claim is made for this seed argument. The complete external question remains the density of nonzero total-domination roots of finite isolate-free graphs throughout the complex plane."))), []));

    private static DocumentBlock Node(string selector, string title, Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("td-seed-" + selector.Replace("_", "-")), DeclarationHandle.Create(Prefix + selector),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Par(Seq(V(name), Colon, type)), Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) => Seq(Exists, Sp, Par(Seq(V(name), Colon, type)), Comma, Sp, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula SeedRoot(bool actual)
    {
        Formula p = actual ? Call("totalPolynomial", Call("seedGraph", Call("square", V("s")))) : Call("seedPolynomial", Call("square", V("s")));
        Formula body = And(Lt(Seq(Minus, V("1")), V("r")), And(Lt(V("r"), Seq(Minus, V("1"), Plus, new Formula.Fraction(V("1"), V("s")))), Call("IsRoot", p, V("r"))));
        if (actual) body = And(body, And(Seq(p, Sp, Ne, Sp, V("0")), All("v", Call("SeedVertex", V("s")), Some("u", Call("SeedVertex", V("s")), Call("Adj", Call("seedGraph", Call("square", V("s"))), V("v"), V("u")))));
        return All("s", Nat, Imp(And(Le(V("3"), V("s")), Call("Odd", V("s"))), Some("r", Real, body)));
    }
}
