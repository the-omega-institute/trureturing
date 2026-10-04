using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class ActualCoarseReadoutHistoryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/ActualCoarseReadoutHistory.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coarse-observable actual tree strategies separate distinct nonconflicting positives at a fresh nonleaf query, forcing saturated shared histories to incur two nonleaf payments on one input.",
        H("Fresh Coarse Divergence and Saturated Shared Histories"),
        Blocks(
            Paragraph(Text("Sources, addresses, four-valued replies, globally correct strategies, terminal histories and paid sets are the original actual-tree objects. A strategy terminates correctly on every finite source from the same empty initial history. No uniform fuel bound, source description, or finite-family promise is assumed. The coarse readout is the existing leafLabel: alpha is some(true), beta is some(false), while branch and absent both give none. L(W) denotes the existing leafAddresses(W).")),
            Def("kappa", "Coarse reply map", "Kappa sends alpha to some(true), beta to some(false), and both branch and absent to none. The reply carrier is Option Bool."),
            Def("kappa_hist", "Chronological coarse histories", "KappaHist maps each original report to its address and coarse reply. It preserves order, length and repeated requests. The coarse history carrier H is the existing dependent history type over Address with constant response type Option Bool."),
            Def("CoarseObservable", "Coarse-observable original policies", "A policy p is coarse-observable when p(a)=p(b) whenever kappaHist(a)=kappaHist(b), for all raw histories a and b, including histories not reached on any source. The strategy, execution and fee definitions are unchanged."),
            Describe.Lean(DescribeId.Create("actual-coarse-readout-shared-history-obstruction"),
                DeclarationHandle.Create(Prefix + "shared_history_obstruction"),
                H("Fresh divergence and saturated nonleaf excess"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("In the formula, T(pi,W)=kappaHist(terminal(pi,W).history), J(pi,W)=paid(terminal(pi,W).history), and A(g) is the finite set of addresses occurring in the coarse history g. concat is chronological list concatenation, report(q,r) is the dependent address-response pair, and one(a) is the singleton list. prefix means List.IsPrefix; diff is finite-set difference; card and nonempty have their ordinary finite-set meanings. Positive is membership in the third native Fibonacci substitution image, and NC is the existing Nonconflict predicate. O(pi.policy) means CoarseObservable(pi.policy).")),
                    Paragraph(Text("For any common coarse terminal prefix h, the history s extends it to a first differing coarse reply. Coarse observability synchronizes the query at each matching step. Complete compulsory leaf acquisition and literal frontier rigidity rule out identical coarse terminal histories. A repeated address has already fixed its truthful reply on both inputs, so the separating query is fresh. Nonconflict excludes differing labels at a shared leaf. If both inputs have already paid a nonleaf on h, the input for which the fresh query is a nonleaf therefore has two distinct nonleaf payments.")),
                    Paragraph(Text("A common raw history cannot replace a common coarse history: branch and absent may already differ while their coarse reports remain equal. The theorem concerns saturated shared histories and the minimal coarse interface. Joint completion, fallback and cache contracts, finite-family pruning, and endpoint classifications are outside its statement."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Def(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("actual-coarse-readout-" + name.ToLowerInvariant().Replace("_", "-")),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula V(string s) => F.Id(s);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula Some(string name, Formula type, Formula body) => Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula And(params Formula[] xs) => Seq(xs.Select((x, i) => i == 0 ? Par(x) : Seq(Sp, Land, Sp, Par(x))).ToArray());
    private static Formula Or(Formula a, Formula b) => Seq(Par(a), Sp, Lor, Sp, Par(b));
    private static Formula Not(Formula f) => Seq(Neg, Sp, Par(f));
    private static Formula Ne(Formula a, Formula b) => Seq(a, Sp, Neq, Sp, b);
    private static Formula In(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula Le(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);

    private static Formula ResultFormula()
    {
        Formula pi = V("pi"), u = V("U"), v = V("V"), h = V("h"), s = V("s"), q = V("q");
        Formula source = Call("Source"), history = V("H"), address = Call("Address");
        Formula T(Formula w) => Call("T", pi, w);
        Formula J(Formula w) => Call("J", pi, w);
        Formula L(Formula w) => Call("L", w);
        Formula A(Formula g) => Call("A", g);
        Formula Label(Formula w) => Call("leafLabel", w, q);
        Formula Diff(Formula a, Formula b) => Call("diff", a, b);
        Formula Cat(Formula a, Formula b) => Call("concat", a, b);
        Formula Prefix(Formula a, Formula b) => Call("prefix", a, b);
        Formula Next(Formula w) => Cat(Cat(h, s), Call("one", Call("report", q, Label(w))));
        Formula Nonempty(Formula a) => Call("nonempty", a);
        Formula saturation = Imp(And(Nonempty(Diff(A(h), L(u))), Nonempty(Diff(A(h), L(v)))),
            Or(Le(D(2), Call("card", Diff(J(u), L(u)))), Le(D(2), Call("card", Diff(J(v), L(v))))));
        Formula conclusion = Some("s", history, Some("q", address, And(
            Prefix(Next(u), T(u)), Prefix(Next(v), T(v)), Ne(Label(u), Label(v)),
            Not(In(q, A(Cat(h, s)))), Or(Not(In(q, L(u))), Not(In(q, L(v)))), saturation)));
        Formula premises = And(Call("Positive", u), Call("Positive", v), Ne(u, v), Call("NC", u, v),
            Prefix(h, T(u)), Prefix(h, T(v)));
        return All("pi", Call("Strategy"), Imp(Call("O", Call("policy", pi)),
            All("U", source, All("V", source, All("h", history, Imp(premises, conclusion))))));
    }
}
