using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.SourceCoordinates;

internal sealed class NativeRotationDepthGapDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/SourceCoordinates/NativeRotationDepthGap.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One contextual rotation attains the entire Fibonacci word and geometry fiber depth range.",
        H("Native Rotation and Complete Fiber Depth Extrema"),
        Blocks(
            Paragraph(Text("S is the actual FreeMagma Bool source: finite nonempty ordered binary trees. "
                + "Alpha is the true leaf, beta the false leaf, and pair retains the original ordered brackets. "
                + "The original substitution rho sends alpha to beta and beta to pair(beta,alpha). "
                + "R(k,t) is its k-fold iterate, including k=0. T(n)=R(n,alpha); U(n) is the existing "
                + "AncestorAreaInstability.rotated(n-3), with U(3)=pair(beta,pair(alpha,beta)). "
                + "T(3)=pair(pair(beta,alpha),beta). The word w(t)=wd(t) retains every labelled leaf "
                + "in its original order; ell(t) counts all leaves. G is the original five-coordinate "
                + "geometry of that whole word. Depth and Q are the original intrinsic substitution "
                + "coordinates, with Boolean true written 1 and false written 0.")),
            Definition("ContextRotation", "One Contextual Associativity Step",
                All("C", Context, All("s", Source, All("t", Source,
                    IffOf(Call("ContextRotation", V("C"), V("s"), V("t")),
                        Some("a", Source, Some("b", Source, Some("c", Source, And(
                            EqOf(V("s"), Plug(V("C"), Mul(Mul(V("a"), V("b")), V("c")))),
                            EqOf(V("t"), Plug(V("C"), Mul(V("a"), Mul(V("b"), V("c"))))))))))))),
                "C is the existing ActualLeafHistoryRigidity.OutputContext. Plugging its unique hole "
                + "preserves every ordered sibling and label. ContextRotation uses one local associativity move."),
            Definition("rotationGraph", "Actual Undirected Rotation Graph",
                All("s", Source, All("t", Source, IffOf(Adj(V("s"), V("t")), And(
                    NeOf(V("s"), V("t")), Some("C", Context, OrOf(
                        Call("ContextRotation", V("C"), V("s"), V("t")),
                        Call("ContextRotation", V("C"), V("t"), V("s")))))))),
                "The graph has the entire actual source as its vertex set. Its edges are either "
                + "orientation of a contextual ordered associativity step between distinct sources. "
                + "d is the ordinary SimpleGraph.dist and Reachable is graph reachability. "
                + "For disconnected pairs ordinary distance is zero; the universal metric claim retains Reachable."),
            Definition("leftContext", "Native Left Context",
                And(EqOf(Call("C", D(0)), Call("hole")), All("k", Nat,
                    EqOf(Call("C", Add(V("k"), D(1))),
                        Call("left", Call("C", V("k")), Tree(Add(V("k"), D(2))))))),
                "C(k) denotes leftContext(k). Its right siblings are the original T(k+2), "
                + "while its hole follows k left edges. In addresses false means left."),
            Describe.Lean(DescribeId.Create("native-rotation-depth-gap"),
                DeclarationHandle.Create(Prefix + "native_rotation_depth_gap"),
                H("Single Rotation, Forward Transport, and Sharp Complete Fiber Bounds"),
                StatementSource.FromAuthor(And(
                    All("n", Nat, Imp(LeOf(D(3), V("n")), Family(V("n")))),
                    NegOf(Some("A", Real, All("s", Source, All("t", Source,
                        Imp(EqOf(Word(V("s")), Word(V("t"))),
                            Imp(Call("Reachable", V("s"), V("t")),
                                LeOf(Abs(Sub(Cast(Depth(V("s"))), Cast(Depth(V("t"))))),
                                    Times(V("A"), Cast(Dist(V("s"), V("t"))))))))))))),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The structural induction on C(k) uses the source centralizer "
                        + "recurrence T(k+4)=pair(T(k+3),T(k+2)). It identifies C(k).plug(T(3)) with "
                        + "T(k+3) and C(k).plug(U(3)) with rotated(k), at the exact address L repeated k times. "
                        + "Thus the original three-leaf reassociation remains one edge at every n>=3. "
                        + "The existing AncestorAreaInstability.result supplies the whole-word equality, "
                        + "Fibonacci leaf count and the two endpoint depths. Unequal depths make the sources "
                        + "distinct, so adjacency gives distance exactly one.")),
                    Paragraph(Text("The existing intrinsic coordinate composites identify the ray flag and "
                        + "supply the one-step coordinate transport. Iteration gives depths n+j and j. "
                        + "The original GeometryEntranceRatio.wd_substitution gives w(rho(t))=sigma(w(t)), "
                        + "so every common forward iterate has the same entire labelled word and hence the same G. "
                        + "No rotation-distance assertion is made about these common forward iterates.")),
                    Paragraph(Text("For every actual ancestor p and exponent k, the composition transport "
                        + "and Fibonacci recurrence give ell(R(k,p))=fib(k+1) composition(p).1 "
                        + "+ fib(k+2) composition(p).2, at least fib(k+1) because ell(p)>0. "
                        + "Applying this estimate to the realized maximal ancestor bounds every actual tree "
                        + "of length fib(n+1) by depth n, using strict Fibonacci growth for n>=3. "
                        + "Same words have the same length by FreeMagma.length_toFreeSemigroup. "
                        + "The original GeometryEntranceRatio.tree_length also fixes the length of every "
                        + "member of the complete same-G fiber. Both fibers therefore have minimum zero "
                        + "and maximum n, attained by these same U(n) and T(n). There is no restriction "
                        + "to the displayed family, selected shapes, or selected word representatives.")),
                    Paragraph(Text("If a finite real coefficient A bounded depth differences for all "
                        + "same-word reachable pairs, these distance-one witnesses would give n<=A for "
                        + "every n>=3, contradicting unbounded natural numbers. The result connects "
                        + "native contextual rotation with the intrinsic depth coordinate. It is a "
                        + "repository-derived synthesis of the cited family and coordinate results, "
                        + "with no global priority claim, quotient adjacency, physical acquisition claim, "
                        + "or bound for arbitrary non-Fibonacci leaf counts."))), DescribeRole.Theorem))));

    private static Formula V(string s) => F.Id(s);
    private static Formula Source => V("S");
    private static Formula Context => Call("OutputContext");
    private static Formula Nat => Call("Nat");
    private static Formula Real => Call("Real");
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula NeOf(Formula a, Formula b) => Seq(a, Sp, Neq, Sp, b);
    private static Formula LeOf(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula Add(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula Sub(Formula a, Formula b) => Seq(a, Sp, Minus, Sp, b);
    private static Formula Times(Formula a, Formula b) => Seq(Par(a), Sp, Cdot, Sp, Par(b));
    private static Formula Abs(Formula a) => Seq(Lvert, Sp, a, Sp, Rvert);
    private static Formula Cast(Formula a) => Call("real", a);
    private static Formula NegOf(Formula f) => Seq(Neg, Sp, Par(f));
    private static Formula IffOf(Formula a, Formula b) => Seq(Par(a), Sp, Iff, Sp, Par(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula OrOf(Formula a, Formula b) => Seq(Par(a), Sp, Lor, Sp, Par(b));
    private static Formula And(params Formula[] xs) => Seq(xs.Select((x, i) =>
        i == 0 ? Par(x) : Seq(Sp, Land, Sp, Par(x))).ToArray());
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula Pair(Formula a, Formula b) => Par(Seq(a, Comma, Sp, b));
    private static Formula Mul(Formula a, Formula b) => Call("pair", a, b);
    private static Formula Plug(Formula c, Formula t) => Call("plug", c, t);
    private static Formula Tree(Formula n) => Call("T", n);
    private static Formula Other(Formula n) => Call("U", n);
    private static Formula Word(Formula t) => Call("w", t);
    private static Formula Length(Formula t) => Call("ell", t);
    private static Formula Depth(Formula t) => Call("depth", t);
    private static Formula Coord(Formula t) => Call("Q", t);
    private static Formula R(Formula j, Formula t) => Call("R", j, t);
    private static Formula Adj(Formula s, Formula t) => Call("Adj", s, t);
    private static Formula Dist(Formula s, Formula t) => Call("d", s, t);
    private static Formula Geometry(Formula t) => Call("G", Word(t));
    private static DocumentBlock Definition(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("native-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Family(Formula n)
    {
        Formula c = Call("C", Sub(n, D(3))), t = Tree(n), u = Other(n), j = V("j"), s = V("s");
        return And(
            EqOf(Call("holeAddress", c), Call("replicate", Sub(n, D(3)), D(0))),
            EqOf(Plug(c, Tree(D(3))), t), EqOf(Plug(c, Other(D(3))), u),
            Call("ContextRotation", c, t, u), Adj(t, u), EqOf(Dist(t, u), D(1)),
            EqOf(Word(t), Word(u)), EqOf(Length(t), Call("fib", Add(n, D(1)))),
            EqOf(Length(u), Call("fib", Add(n, D(1)))),
            EqOf(Coord(t), Pair(n, D(1))), EqOf(Coord(u), Pair(D(0), D(0))),
            All("j", Nat, And(EqOf(Word(R(j, t)), Word(R(j, u))),
                EqOf(Geometry(R(j, t)), Geometry(R(j, u))),
                EqOf(Depth(R(j, t)), Add(n, j)), EqOf(Depth(R(j, u)), j))),
            All("s", Source, Imp(EqOf(Word(s), Word(t)),
                And(LeOf(D(0), Depth(s)), LeOf(Depth(s), n)))),
            All("s", Source, Imp(EqOf(Geometry(s), Geometry(t)),
                And(LeOf(D(0), Depth(s)), LeOf(Depth(s), n)))),
            EqOf(Depth(t), n), EqOf(Depth(u), D(0)));
    }
}
