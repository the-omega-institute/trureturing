using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.LinearForests;

internal sealed class CompatibleCycleInventoryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/LinearForests/CompatibleCycleInventory.";
    private static Formula Parenthesized(Formula x) => Seq(Left, Open, x, Right, Close);
    private static Formula V(string n) => F.Id(n);
    private static Formula N(string n) => new Formula.NamedConstant(FormulaIdentifier.Create(n));
    private static Formula All(string n, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Ex(string n, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), t, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula If(Formula p, Formula y, Formula n) => Call("ite", p, y, n);
    private static Formula Card(Formula x) => Call("card", x);
    private static Formula Fac(Formula x) => Call("factorial", x);
    private static Formula Inv(byte a, byte b) => Call("inventory", V("s"), V("d"), D(a), D(b));
    private static Formula Side(byte b) => Call("Side", V("s"), D(b));
    private static Formula Let(string n, Formula t, Formula x, Formula b) =>
        Parenthesized(Seq(N("let"), Sp, V(n), Colon, Sp, t, Sp, F.Eq, Sp, x, Semi, Sp, b));
    private static Formula Finite(Formula x, Formula b) =>
        Seq(OpenBracket, Call("Finite", x), CloseBracket, Comma, Sp, b);
    private static Formula At(string f, Formula x) => Call("apply", V(f), x);
    private static Formula C(string n) => Call(n, V("E"));
    private static Formula Omega() => Call("AlternatingCompletion", V("E"), V("k"));
    private static Formula Maps(Formula c) => Call("BoolMaps", c);
    private static Formula Count(Formula zero, Formula m, Formula p, Formula q) =>
        If(zero, D(0), If(Lt(D(0), m),
            Multiply(Multiply(m, Fac(Subtract(Add(m, p), D(1)))), Fac(Subtract(Add(m, q), D(1)))),
            If(Equal(Multiply(p, q), D(0)), Fac(Subtract(Add(p, q), D(1))), D(0))));

    private static Formula InventoryStatement() => All("C", N("Type"),
        Finite(V("C"), All("s", Maps(V("C")), All("d", Maps(V("C")),
        Imp(Equal(Inv(0, 1), Inv(1, 0)),
            Equal(Card(Call("Compatible", V("s"), V("d"))),
                If(Equal(Card(V("C")), D(0)), D(0),
                    If(Lt(D(0), Inv(0, 1)),
                        Multiply(Multiply(Inv(0, 1), Fac(Subtract(Card(Side(0)), D(1)))),
                            Fac(Subtract(Card(Side(1)), D(1)))),
                        If(Or(Equal(Inv(0, 0), D(0)), Equal(Inv(1, 1), D(0))),
                            Fac(Subtract(Card(V("C")), D(1))), D(0))))))))));

    private static Formula Member(string f) => All("A", C("Component"),
        Equal(Call("component", V("E"), Call("value", At(f, V("A")))), V("A")));
    private static Formula Connector() => All("sigma", Omega(), All("A", C("Component"),
        Equal(Call("apply", Call("value", V("sigma")), Call("value", At("t", V("A")))),
            Call("value", At("h", Call("apply", Call("value", At("Phi", V("sigma"))), V("A")))))));
    private static Formula Data()
    {
        var body = And(Equal(V("a"), V("b")),
            And(Equal(Card(C("Component")), Add(Add(Add(V("a"), V("b")), V("p")), V("q"))),
            And(Imp(Call("Nonzero", V("n")), Lt(D(0), Card(C("Component")))),
                Equal(Card(Omega()), Count(Equal(V("n"), D(0)), V("a"), V("p"), V("q"))))));
        body = Let("q", N("Nat"), Inv(1, 1), body);
        body = Let("p", N("Nat"), Inv(0, 0), body);
        body = Let("b", N("Nat"), Inv(1, 0), body);
        body = Let("a", N("Nat"), Inv(0, 1), body);
        body = Let("d", Maps(C("Component")), Call("oppositeTailColor", V("k"), V("t")), body);
        return Let("s", Maps(C("Component")), Call("headColor", V("k"), V("h")), body);
    }
    private static Formula Conclusion() =>
        Ex("t", Call("Equiv", C("Component"), C("Tail")),
        Ex("h", Call("Equiv", C("Component"), C("Head")),
        Ex("Phi", Call("Equiv", Omega(),
            Call("Compatible", Call("headColor", V("k"), V("h")),
                Call("oppositeTailColor", V("k"), V("t")))),
            And(Member("t"), And(Member("h"), And(Connector(), Data()))))));
    private static Formula RawStatement() => All("V", N("Type"),
        Finite(V("V"), All("n", N("Nat"), All("E", Call("Relation", V("V")),
        All("k", Maps(V("V")), Imp(
            And(C("RightUnique"), And(C("LeftUnique"), And(C("Acyclic"),
            And(Call("EdgeAlternating", V("E"), V("k")),
            And(Equal(Card(Call("Side", V("k"), D(0))), V("n")),
                Equal(Card(Call("Side", V("k"), D(1))), V("n"))))))), Conclusion()))))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual labelled alternating completions of every finite balanced two-color directed linear forest are exhaustively classified by compatible cycles on its true components and have the four endpoint-inventory counts.",
        H("Alternating completion inventories"),
        Blocks(
            Describe.Lean(DescribeId.Create("inventory"),
                DeclarationHandle.Create(Prefix + "compatible_cycle_card"),
                H("Exhaustive two-state inventory count"),
                StatementSource.FromAuthor(Disp(InventoryStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("C is any finite labelled type. BoolMaps(C) means C to Bool; the displayed states 0 and 1 mean false and true. Side(s,b) is the subtype of labels x with s(x)=b. inventory(s,d,a,b) is the cardinality of labels x with s(x)=a and d(x)=b. Compatible(s,d) consists of actual permutations rho of C with Nonempty(C), rho.IsCycleOn(univ), and d(x)=s(rho(x)) for every x. Thus the empty carrier has no compatible cycles, while the identity on a singleton is accepted exactly when its states agree. ite is the ordinary if-then-else; all factorial arguments use natural subtraction.")),
                    Paragraph(Text("Interpret every label x as an auxiliary arc from s(x) to d(x). Labels are never merged, including parallel arcs and loops. For a label c with s(c)=d(c), deleting c from an actual cycle leaves its actual successor y as an insertion slot of state s(c). Conversely, swap(none,some(y)) composed with optionCongr(rho) inserts the deleted label immediately before y. Mathlib Perm.decomposeOption proves exhaustive inverse reconstruction on the whole permutation carrier. The first-return comparison through the retained labels proves single-cycle equivalence; compatibility is equivalent to s(y)=s(c) together with compatibility of the retained cycle. This is a product equivalence with all slots and all compatible retained cycles, not an image-defined completion set.")),
                    Paragraph(Text("When there are no loops, the balanced inventory consists of m arcs in each direction. Every compatible permutation is uniquely specified by a bijection f from the false fiber to the true fiber and a bijection g back. It is a single cycle exactly when the first-return permutation f followed by g is a single cycle on the false fiber. Consequently the exhaustive carrier is equivalent to the product of all f and all full cycles of the false fiber. Existing unrestricted cycle counting gives m! times (m-1)!. Strong induction deletes loops using the exhaustive insertion equivalence; the number of actual insertion slots is the remaining cardinality of the corresponding source fiber. The factorial recurrence yields m(r-1)!(t-1)!, with r and t the two source-fiber sizes. This inference is consumed by the original forest completion count below.")),
                    Paragraph(Text("If both crossing inventories vanish, compatibility preserves s. A single orbit forces s constant. If one loop inventory is empty, every permutation cycle is compatible and the count is (card(C)-1)!. If both loop inventories are nonempty, no full cycle is compatible. The separate empty-carrier case prevents the natural-subtraction factorial convention from creating an empty cycle.")),
                    Paragraph(Text("The classical count is the two-vertex specialization of the BEST Euler-tour formula for labelled directed multigraphs: Creed and Cryan, The Number of Euler Tours of Random Directed Graphs, Electronic Journal of Combinatorics 20(3), P13, DOI 10.37236/2377, Theorem 1, pages 2-3. Its tours are identified modulo cyclic rotation, with loops and parallel arcs allowed. For m positive the rooted in-tree count is m and the outdegrees are m+p and m+q. The Lean proof instead supplies the explicit deletion and first-return inventory equivalences. It imports no general BEST theorem and makes no novelty claim."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("forest"),
                DeclarationHandle.Create(Prefix + "alternating_completion_classification"),
                H("The original raw forest and all four cases"),
                StatementSource.FromAuthor(Disp(RawStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("V is any finite labelled type, n is any natural number, E is a binary relation and k:V to Bool colors exactly n vertices false and n vertices true. RightUnique and LeftUnique express at most one outgoing and incoming E-edge respectively. Acyclic means that Relation.TransGen(E) is irreflexive. EdgeAlternating means k(x) differs from k(y) for every E(x,y). No extension, path decomposition, connectivity or positive-count premise is assumed.")),
                    Paragraph(Text("Component(E) is the quotient of all V by Relation.EqvGen(E), including isolated vertices. Head(E) and Tail(E) are the actual vertices with no incoming and no outgoing E-edge. The supplied equivalences h and t identify every component with its unique actual head and tail; both membership equations remain part of the statement. component(E,x) denotes the quotient class, and value denotes the underlying value of a subtype. AlternatingCompletion(E,k) consists of actual permutations sigma with Nonempty(V), sigma.IsCycleOn(univ), sigma(x)=y for every E(x,y), and k(sigma(x)) different from k(x) for every x.")),
                    Paragraph(Text("headColor(k,h)(A)=k(h(A)) and oppositeTailColor(k,t)(A)=not(k(t(A))). Therefore d(A)=s(tau(A)) is exactly k(t(A)) different from k(h(tau(A))). Phi is an equivalence onto all compatible actual nonempty single-cycle permutations of Component(E), and the displayed connector equation is sigma(t(A))=h(Phi(sigma)(A)) for every sigma and A. It is obtained by restricting the original DirectedForestCompletion.full_cycle_completion_equiv: internal edges use the supplied edge-color condition; at actual tails the original connector equation gives both directions. Nonemptiness is transported through the actual quotient map, explicitly excluding the empty full-cycle convention of that supplier.")),
                    Paragraph(Text("The inventories a,b,p,q are respectively the actual component endpoint types (false,false), (true,true), (false,true), and (true,false). They retain original labels. The existing edgeEquiv pairs vertices with an outgoing edge with vertices with an incoming edge. Restricting it by the given edge colors pairs occupied false outgoing vertices with occupied true incoming vertices. Splitting the two equally sized raw color fibers gives card(Tail false)=card(Head true). Transport through t and h then gives a=b. No path decomposition or component color-sum premise is supplied.")),
                    Paragraph(Text("Write m=a=b. The statement gives card(Component(E))=a+b+p+q, and this cardinality is positive whenever n is nonzero. The four cases are: n=0 gives zero completions; n positive and m positive gives m(m+p-1)!(m+q-1)!; n positive and m=0 with pq=0 gives (p+q-1)!; n positive and m=0 with both p and q positive gives zero. In the third and fourth cases p+q is positive by the component cardinality equation. In particular p+q=1 is permitted: the unique component cycle is its identity and the actual path closes by its tail-to-head edge.")),
                    Paragraph(Text("Ordinary forest contraction is reused from the original declarations, rather than proved again. Its classical provenance is Tsaban, Permutation graphs, fast forward permutations, and sampling the cycle structure of a permutation, DOI 10.1016/S0196-6774(03)00017-8, Lemmas 1.1-1.5, pages 107-109. Existing source attributions and licenses in DirectedForestCompletion remain applicable. This result counts directed cycles modulo rotation only. It makes no undirected reversal, adaptive-history, posterior, oracle, query-bound, configuration multiplicity or welded-tree EXIT assertion."))),
                DescribeRole.Theorem)), []));
}
