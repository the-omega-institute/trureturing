using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.SourceCoordinates;

internal sealed class ExactSharingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/SourceCoordinates/ExactSharing.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact expanded size, rooted sharing and binary-call count of the Fibonacci source.",
        H("Exact Sharing and Pure Fibonacci Evaluation"),
        Blocks(
            Paragraph(Text("S is the existing FreeMagma Bool of nonempty ordered binary trees. "
                + "Alpha is of(true), beta is of(false), and pair(s,t) retains both ordered ports and all brackets. "
                + "The existing substitution rho sends alpha to beta and beta to pair(beta,alpha), preserving pairs. "
                + "T(n)=rho^n(alpha), so T(0)=alpha, T(1)=beta and T(n+2)=pair(T(n+1),T(n)). "
                + "The leaf count ell is FreeMagma.length. Composition c records the two labelled leaf counts, "
                + "and B(n)=atomicBlock(n) is the existing iterated composition step (a,b) to (b,a+b). "
                + "All indices are natural numbers, subtraction is truncated natural subtraction, and fib(0)=0, fib(1)=1.")),
            Definition("expandedNodes", "Expanded Node Count",
                ExpandedFormula(),
                "N(t)=expandedNodes(t) counts every leaf and every internal node of the expanded tree."),
            Definition("fringes", "Rooted Fringe Set",
                FringeFormula(),
                "Sub(t)=fringes(t) is a finite set of actual rooted fringe trees. It contains the root and "
                + "recursively both children's fringes, identifying only exactly equal trees. It is the exact "
                + "distinct-fringe set used below for the source-level sharing count. Every retained node occurs "
                + "below the root; orbit terms absent from the tree are excluded. Labels, ports and brackets "
                + "participate in equality. A separate DAG object or minimality theorem is outside this declaration."),
            Definition("evalStep", "One Counted Binary Call",
                StepFormula(),
                "A is any type in an arbitrary universe. A state is a triple (previous,current,calls). "
                + "Step(m,s)=evalStep(m,s) reads the two saved values, invokes m(current,previous) once, "
                + "retains current as the next previous value and increments calls by one. No associativity "
                + "or commutativity is assumed of the binary operation."),
            Definition("sharedEval", "Evaluation from Supplied Leaf Values",
                SharedFormula(),
                "Shared(m,a,b,n)=sharedEval(m,a,b,n). In the formula, run(m,a,b,n) means the "
                + "(n-1)-fold iterate of step(m,-) on (a,b,0). At n=0 the result is (a,0); "
                + "otherwise it is the current value and counter from that run. The input leaf values "
                + "a and b are already supplied. The run stores only the two consecutive values and a counter."),
            Describe.Lean(DescribeId.Create("exact-sharing"), DeclarationHandle.Create(Prefix + "exact_sharing"),
                H("Exact Expanded Size, Rooted Fringe Size, and Pure Evaluation"),
                StatementSource.FromAuthor(Result()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every n, the source composition equals B(n), its leaf count is fib(n+1), "
                        + "and its expanded node count is 2 fib(n+1)-1. Its complete fringe set is the singleton "
                        + "{T(n)} when n<2, and the image of range(n+1) under T otherwise. Thus the formal "
                        + "source-level fringe count is one at n=0,1 and n+1 at every n>=2. In particular the "
                        + "other labelled leaf is absent at each singleton stage.")),
                    Paragraph(Text("The source centralizer supplies the ordered orbit recurrence, and the existing "
                        + "iterate_length theorem supplies its leaf count. Structural induction gives "
                        + "N(t)=2 ell(t)-1 for every nonempty full binary source. The intrinsic primitive-root "
                        + "uniqueness theorem makes the orbit T injective, retaining the distinction between "
                        + "the two initial one-leaf trees. For T(2), all three orbit terms occur. For larger "
                        + "trees the larger child already contains every fringe of the smaller child. "
                        + "Adding the new root extends precisely the initial segment of the orbit, so its "
                        + "cardinality is n+1. Composition is the existing CliffordLeafOrbit.result observation.")),
                    Paragraph(Text("For any total interpretation E:S to A preserving pairs by a fixed binary "
                        + "operation m, k iterations of the counted step have state (E(T(k)),E(T(k+1)),k). "
                        + "Induction uses the same ordered recurrence, without any algebraic law on m. "
                        + "The resulting shared evaluation equals (E(T(n)),n-1) for every n, including "
                        + "zero calls at n=0,1. This is an achievable call count; no claim of optimality "
                        + "is made for interpretations with additional identities or constant values.")),
                    Paragraph(Text("Purity is expressed by one function E and one fixed operation m on the whole "
                        + "source. Position, changing environments, histories and side effects are not supplied "
                        + "by this interface. The counter is not a bit-time bound: obtaining leaf values, "
                        + "reading operands, representing intermediate values, storage and writing the requested "
                        + "output have separate costs. Polynomial bit time needs bounds on those encoding and "
                        + "operation costs. A linear count in n is not a polynomial bound in the length of "
                        + "a binary encoding of n. Requesting the expanded tree still requires its full "
                        + "expanded output. These resource qualifications do not follow from the call counter."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Definition(string name, string title, Formula formula, string text) =>
        Describe.Lean(DescribeId.Create("sharing-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))),
            DescribeRole.Definition);
    private static Formula V(string s) => F.Id(s);
    private static Formula Nat => Call("Nat");
    private static Formula Source => V("S");
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula EqOf(Formula x, Formula y) => Seq(x, Sp, Eq, Sp, y);
    private static Formula Add(Formula x, Formula y) => Seq(x, Sp, Plus, Sp, y);
    private static Formula Sub(Formula x, Formula y) => Seq(x, Sp, Minus, Sp, y);
    private static Formula Times(Formula x, Formula y) => Seq(x, Sp, Cdot, Sp, y);
    private static Formula Arrow(Formula x, Formula y) => Seq(x, Sp, To, Sp, y);
    private static Formula All(string s, Formula type, Formula body) =>
        Seq(Forall, Sp, V(s), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula And(params Formula[] xs) => Seq(xs.Select((x, i) =>
        i == 0 ? Par(x) : Seq(Sp, Land, Sp, Par(x))).ToArray());
    private static Formula Imp(Formula x, Formula y) => Seq(Par(x), Sp, Implies, Sp, Par(y));
    private static Formula Tuple(Formula x, Formula y) => Seq(Open, x, Comma, Sp, y, Close);
    private static Formula Triple(Formula x, Formula y, Formula z) =>
        Seq(Open, x, Comma, Sp, y, Comma, Sp, z, Close);
    private static Formula Pair(Formula x, Formula y) => Call("pair", x, y);
    private static Formula N(Formula x) => Call("N", x);
    private static Formula Subtrees(Formula x) => Call("Sub", x);
    private static Formula Tree(Formula x) => Call("T", x);
    private static Formula Previous(Formula x) => Call("previous", x);
    private static Formula Current(Formula x) => Call("current", x);
    private static Formula Count(Formula x) => Call("calls", x);
    private static Formula Binary(Formula a) => Arrow(a, Arrow(a, a));
    private static Formula State(Formula a) => Seq(a, Sp, F.Times, Sp, a, Sp, F.Times, Sp, Nat);
    private static Formula ApplyMu(Formula m, Formula x, Formula y) => Call("apply", m, x, y);
    private static Formula Shared(Formula m, Formula a, Formula b, Formula n) => Call("sharedEval", m, a, b, n);
    private static Formula Run() => Call("run", V("m"), V("a"), V("b"), V("n"));

    private static Formula ExpandedFormula()
    {
        Formula s = V("s"), t = V("t"), b = V("b");
        Formula leaf = All("b", Call("Bool"), EqOf(N(Call("of", b)), D(1)));
        Formula pair = All("s", Source, All("t", Source,
            EqOf(N(Pair(s, t)), Add(Add(N(s), N(t)), D(1)))));
        return And(leaf, pair);
    }

    private static Formula FringeFormula()
    {
        Formula s = V("s"), t = V("t"), b = V("b");
        Formula leaf = All("b", Call("Bool"),
            EqOf(Subtrees(Call("of", b)), Call("singleton", Call("of", b))));
        Formula pair = All("s", Source, All("t", Source,
            EqOf(Subtrees(Pair(s, t)), Call("insert", Pair(s, t),
                Call("union", Subtrees(s), Subtrees(t))))));
        return And(leaf, pair);
    }

    private static Formula StepFormula()
    {
        Formula a = V("A"), m = V("m"), s = V("s");
        Formula update = Triple(Current(s), ApplyMu(m, Current(s), Previous(s)), Add(Count(s), D(1)));
        Formula eq = EqOf(Call("step", m, s), update);
        return All("A", Call("Type"), All("m", Binary(a), All("s", State(a), eq)));
    }

    private static Formula SharedFormula()
    {
        Formula a = V("A"), m = V("m"), x = V("a"), y = V("b"), n = V("n");
        Formula eq = EqOf(Shared(m, x, y, n), Call("ite", EqOf(n, D(0)), Tuple(x, D(0)),
            Tuple(Current(Run()), Count(Run()))));
        return All("A", Call("Type"), All("m", Binary(a), All("a", a, All("b", a, All("n", Nat, eq)))));
    }

    private static Formula Result()
    {
        Formula n = V("n"), a = V("A"), m = V("m"), e = V("E");
        Formula t = Tree(n);
        Formula small = Seq(n, Sp, Lt, Sp, D(2));
        Formula smallCase = Imp(small, And(
            EqOf(Subtrees(t), Call("singleton", t)), EqOf(Call("card", Subtrees(t)), D(1))));
        Formula largeCase = Imp(Seq(D(2), Sp, Le, Sp, n), And(
            EqOf(Subtrees(t), Call("image", V("T"), Call("range", Add(n, D(1))))),
            EqOf(Call("card", Subtrees(t)), Add(n, D(1)))));
        Formula ApplyE(Formula x) => Call("E", x);
        Formula mapLaw = All("s", Source, All("t", Source,
            EqOf(ApplyE(Pair(V("s"), V("t"))), ApplyMu(m, ApplyE(V("s")), ApplyE(V("t"))))));
        return And(All("n", Nat, And(
                EqOf(Call("c", t), Call("B", n)),
                EqOf(Call("ell", t), Call("fib", Add(n, D(1)))),
                EqOf(N(t), Sub(Times(D(2), Call("fib", Add(n, D(1)))), D(1))),
                smallCase, largeCase)),
            All("A", Call("Type"), All("m", Binary(a), All("E", Arrow(Source, a),
                Imp(mapLaw, All("n", Nat, EqOf(Shared(m, ApplyE(V("alpha")), ApplyE(V("beta")), n),
                    Tuple(ApplyE(t), Sub(n, D(1))))))))));
    }
}
