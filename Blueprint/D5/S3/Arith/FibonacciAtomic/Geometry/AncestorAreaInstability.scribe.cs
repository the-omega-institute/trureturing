using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Geometry;

internal sealed class AncestorAreaInstabilityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Geometry/AncestorAreaInstability.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The prescribed native Fibonacci trees have equal complete leaf words and unbounded intrinsic-depth gaps despite a fixed ancestor-area distance and vanishing normalized distance.",
        H("Ancestor Area and Intrinsic Depth Instability"), Blocks(
            Paragraph(Text("The sources are the existing FreeMagma Bool trees: true denotes alpha, false denotes beta, and pairing preserves both child order and every leaf label. The coordinate list is the existing inorder ancestor-area list, with each internal node contributing the product of its actual child leaf counts at its own gap.")),
            Def("depth", "Intrinsic inverse-substitution depth",
                "depth(t) is the supremum of the natural exponents k for which an actual source p satisfies substitution iterated k times on p equals t. The proof establishes that this set is finite and nonempty for every source. Its supremum is therefore attained and is the maximal actual inverse-substitution exponent. It is not the height of an address."),
            Def("T", "The alpha generation ray",
                "T(n) is substitution iterated n times on the alpha leaf."),
            Def("rotated", "The prescribed rotated sources",
                "rotated(0) is pair(beta,pair(alpha,beta)). The recursive member rotated(k+1) is pair(rotated(k),T(k+2)). Thus the leftmost three-leaf subtree is rotated once, while every appended right subtree is retained."),
            Def("U", "Indexing by generation",
                "U(n) is rotated(n-3). For every n at least three, U(3) is pair(beta,pair(alpha,beta)) and U(n+1) is pair(U(n),T(n-1)). The extension to n below three is unused by the family assertions."),
            Def("readout", "The full ancestor-area readout",
                "readout(m,t) casts the existing coordinate list to real values at each gap position. At the actual leaf count m=length(t), the coordinate list has exactly m-1 entries, so no padding contributes. Default zero is used only for indices outside the list. In the displayed statement, real(k) is the canonical natural-to-real cast."),
            Def("normalized", "Total-area normalization",
                "normalized(m,t) divides every coordinate of readout(m,t) by the natural binomial coefficient choose(m,2), cast to the reals. For the prescribed sources at n at least three, m=fib(n+1) and this denominator is positive."),
            Def("ltwo", "Euclidean distance",
                "ltwo(x,y) is the square root of the sum over all Fin(m-1) positions of the square of x(i)-y(i). The norm of the full vector in the theorem is the ordinary finite product supremum norm."),
            Def("midpoint", "A common noisy observation",
                "midpoint(n) is the coordinatewise arithmetic mean of the two full normalized vectors, using the common leaf count length(T(n)). Exactly this same vector is passed to both error tests and to every summary-to-real estimator."),
            Describe.Lean(DescribeId.Create("ancestor-area-instability-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The Full Family and Its Readout Bounds"), StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every n at least three, T(n) and U(n) have the same complete ordered leaf word and fib(n+1) leaves. Their intrinsic depths are n and zero. Their full coordinate lists are [1,2] followed by a common tail and [2,1] followed by that same tail. The difference at the first two actual gaps is therefore (-1,1), with zero difference at every later gap. Its Euclidean norm is sqrt(2) and its supremum norm is one.")),
                    Paragraph(Text("The simultaneous full-family assertion comes from the actual source recursion. The generation ray obeys T(n+2)=pair(T(n+1),T(n)). The rotated sources have no substitution preimage: the three-leaf member has none, and every subsequent pair retains that obstruction in its left child. Injectivity of native substitution and the absence of an alpha preimage give the maximal depth n of T(n). Finiteness of all actual entrances supplies the maximum defining depth for every source.")),
                    Paragraph(Text("The proof directly uses GeometryEntranceRatio.entranceFinite for actual entrance finiteness, SourceTransportCentralizer.source_transport_centralizer for substitution injectivity and the native ray recurrence, CliffordLeafOrbit.result for the ray composition, and the positive atomic-block clause of GraftAffineClosure.result for its Fibonacci components. Leaf-count and coordinate-list length identities are internal interface normalization, not separately delivered theorems or claimed new content.")),
                    Paragraph(Text("No finite real L bounds the intrinsic-depth difference of every equal-leaf-count pair by L times its Euclidean ancestor-area distance. Applying such a bound to this prescribed family would force every n at least three to be at most L*sqrt(2).")),
                    Paragraph(Text("Dividing the full vectors by choose(fib(n+1),2) gives supremum difference exactly its reciprocal. The reciprocal tends to zero as n tends to infinity. The depth difference remains n. For every permitted coordinate-error tolerance epsilon at least half that reciprocal, the same midpoint lies within epsilon of both exact normalized vectors.")),
                    Paragraph(Text("Every real-valued function of that common summary has, on at least one of the two sources, depth error at least n/2. The triangle inequality bounds the sum of its errors below by n, so their maximum is at least n/2. This assertion concerns this ancestor-area readout and its stated coordinate error model; it supplies no lower bound for other observation methods or for acquiring, executing, or storing an observation."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Def(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("ancestor-area-instability-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula V(string name) => F.Id(name);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Op(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Op(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula LeOf(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula Sub(Formula a, Formula b) => Seq(Par(a), Sp, Minus, Sp, Par(b));
    private static Formula Add(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula Mul(Formula a, Formula b) => Seq(a, Sp, Cdot, Sp, b);
    private static Formula Div(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula Abs(Formula x) => Seq(Lvert, Sp, x, Sp, Rvert);
    private static Formula Norm(Formula x) => Seq(Vert, Sp, x, Sp, Vert);
    private static Formula Imp(Formula a, Formula b) =>
        Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula And(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (int i = clauses.Length - 2; i >= 0; --i)
            result = Seq(Par(clauses[i]), Sp, Land, Sp, Par(result));
        return result;
    }
    private static Formula ResultFormula()
    {
        Formula n = V("n"), s = V("s"), t = V("t"), l = V("L"), e = V("epsilon");
        Formula naturals = Seq(Mathbb, Grp(V("N")));
        Formula reals = Seq(Mathbb, Grp(V("R"))), source = Op("Source");
        Formula tn = Call("T", n), un = Call("U", n), m = Call("length", tn);
        Formula fib = Call("fib", Add(n, D(1)));
        Formula denominator = Call("real", Call("choose", fib, D(2)));
        Formula exactT = Call("readout", m, tn), exactU = Call("readout", m, un);
        Formula normT = Call("normalized", m, tn), normU = Call("normalized", m, un);
        Formula family = All("n", naturals, Imp(LeOf(D(3), n), And(
            EqOf(Call("wd", tn), Call("wd", un)), EqOf(m, fib),
            EqOf(Call("length", un), m), EqOf(Call("depth", tn), n),
            EqOf(Call("depth", un), D(0)),
            EqOf(Call("ltwo", exactT, exactU), Seq(Sqrt, Grp(D(2)))),
            EqOf(Norm(Sub(exactT, exactU)), D(1)),
            EqOf(Norm(Sub(normT, normU)), Div(D(1), denominator)))));
        Formula depthDifference = Abs(Sub(Call("real", Call("depth", s)),
            Call("real", Call("depth", t))));
        Formula pairDistance = Call("ltwo", Call("readout", Call("length", s), s),
            Call("readout", Call("length", s), t));
        Formula noL = Seq(Neg, Sp, Par(Ex("L", reals, All("s", source, All("t", source,
            Imp(EqOf(Call("length", s), Call("length", t)),
                LeOf(depthDifference, Mul(l, pairDistance))))))));
        Formula reciprocal = Seq(LambdaLower, Sp, n, Colon, Sp, naturals, Comma, Sp,
            Div(D(1), denominator));
        Formula limit = Call("Tendsto", reciprocal, Op("atTop"), Call("nhds", D(0)));
        Formula mid = Call("midpoint", n);
        Formula estimatorType = Seq(Par(Seq(Call("Fin", Sub(m, D(1))), Sp, To, Sp, reals)),
            Sp, To, Sp, reals);
        Formula bound = All("E", estimatorType, LeOf(Div(Call("real", n), D(2)),
            Call("max", Abs(Sub(Call("E", mid), Call("real", Call("depth", tn)))),
                Abs(Sub(Call("E", mid), Call("real", Call("depth", un)))))));
        Formula noisy = All("n", naturals, Imp(LeOf(D(3), n), All("epsilon", reals,
            Imp(LeOf(Div(D(1), Mul(D(2), denominator)), e), And(
                LeOf(Norm(Sub(mid, normT)), e), LeOf(Norm(Sub(mid, normU)), e), bound)))));
        return Disp(And(family, noL, limit, noisy));
    }

}
