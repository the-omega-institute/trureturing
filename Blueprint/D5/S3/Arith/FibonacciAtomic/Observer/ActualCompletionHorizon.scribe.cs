using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class ActualCompletionHorizonDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionHorizon.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An original normalized completion has a uniform chronological horizon and finite literal address support on each original leaf-budget class.",
        H("Original Completion Horizon and Literal Support"),
        Blocks(
            Paragraph(Text("Sources are the original nonempty finite ordered full binary trees with Boolean leaf labels. Addresses are literal finite Boolean words, and readout has the four original replies alpha, beta, branch and absent. Coarse histories preserve every address, order and repetition while identifying branch with absent. Fix any natural m, any family F from Fin m to Source, any finite three-response passive route p, any decoder from coarse histories to Option (Fin m), any natural N at least one, and any correct original Strategy pi whose policy is exactly h maps to controllerPolicy (compileRaw F decode p []) (encodeHistory (kappa_hist h)). No bound on a route word or a prototype is assumed.")),
            Def("CoarseHistory", "Original coarse histories", "A coarse history is a finite ordered list of address and Option Bool pairs. It retains each literal address and each repeated request."),
            Def("routeHorizon", "Longest syntactic route", "A stop has horizon zero. A query contributes one plus the maximum of its none, some false and some true child horizons. This counts all occurrences, including repeated requests; it is not the number of distinct addresses."),
            Def("routeSupport", "Literal route alphabet", "A stop has empty support. A query contributes its literal word and the supports of all three continuations. An arbitrarily long absent word remains in this finite syntactic union."),
            Def("prototypeMax", "Maximum prototype leaf count", "The maximum is Finset.univ.sup of the original source leaf count (F i).length. The existing duplicate-free leaf-list and leaf-address cardinality identities identify this with (leaves (F i)).length. The empty Fin 0 maximum is zero."),
            Def("prototypeLeaves", "Complete prototype leaf alphabet", "Take the union over every i in Fin m of (leaves (F i)).toFinset. There is no prototype size or address-length cutoff. The empty family gives the empty set."),
            Def("qNFinset", "Original bounded node alphabet", "Take the image of all ActualObserverFiniteTable.BoundedAddress N under Subtype.val. Membership is exactly address length at most N minus one, hence this finite set realizes the original Q_N. Every node of an Allowed N source belongs to it; the original nodes_length supplies the depth bound."),
            Paragraph(Text("In the formula, Route is PassiveProtocol Address (fun _ => Option Bool). H(F,p,N) denotes routeHorizon p + prototypeMax F + (2*N-1), and Qstar(F,p,N) denotes qNFinset N union routeSupport p union prototypeLeaves F. normalizedPolicy(F,decode,p) is exactly h maps to controllerPolicy (compileRaw F decode p []) (encodeHistory (kappa_hist h)). outcome(F,decode,p,U) denotes controllerOutcome (compileRaw F decode p []) U, terminal(pi,U) is the original terminal pair, trace(pi,U) its first component, request(a) is Sigma.fst, RawEntry is an address-reply pair, and stateCard(N,pi) is Fintype.card (ExactState (strategyPrefixes N pi)). The exact allowedSources N carrier enumerates the original Allowed N sources.")),
            Describe.Lean(
                DescribeId.Create("actual-completion-horizon-contract"),
                DeclarationHandle.Create(Prefix + "actual_completion_horizon"),
                H("Original completion bound"), StatementSource.FromAuthor(ContractFormula()),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The terminal/outcome equality holds on every original source U, including sources outside Allowed N. Under Allowed N, the full terminal trace has length at most H and every requested literal address belongs to Qstar. The exact compatible-cache carrier has at most 1 + card(allowedSources N)*(H+1)*2 raised to min(card(Qstar),H) states.")),
                    Paragraph(Text("The acquisition address list is the original nodes preorder, by trace_addresses. Its list count is 2*U.length-1, including both internal nodes and leaves. Since Allowed N U means U.length at most N, acquisition uses at most 2*N-1 requests. A verifier on a remaining list qs uses at most qs.length plus the complete acquisition length: a late mismatch retains every earlier successful request and its mismatch request before the new acquisition. Its literal support lies in qs union the actual nodes. Induction over the three route branches adds one chronological step and one literal route word at each query. At a selected stop, the complete prototype leaf list is bounded by prototypeMax and belongs to prototypeLeaves; at an unselected stop, acquisition begins immediately.")),
                    Paragraph(Text("For exact normalized execution, compare raw and normalized controller actions only on prefixes of the actual outcome. A prototype leaf has alpha or beta reply, so choosing the branch representative for coarse none cannot turn a failed test into a successful leaf test. The verifier induction retains leaf membership for every remaining tail; an arbitrary query list would not justify this comparison. Route control sees only kappa, and the representative preserves kappa. At fallback, acquisition_prefix_representative fixes actual acquisition prefixes. Prefix action agreement transfers the raw execution supplied by phase_foundation to the normalized policy on the same source and with the same full trace and bit. The existing execution uniqueness in source_foundation then identifies that execution with terminal pi U.")),
                    Paragraph(Text("The horizon and support inequalities supply the two hypotheses of strategy_state_card_bound at the original N. Each retained coarse prefix has at most H steps and at most card(Qstar) distinct addresses. Only first coarse-none addresses contribute the compatible branch/absent choices. Prefix counting contributes card(allowedSources N)*(H+1), and the absorbing sink contributes one. This state estimate includes nominal ghost cache lifts."))), DescribeRole.Theorem),
            Paragraph(Text("For the source-facing application, positivity of every prototype belongs to completion_contract: it supplies a correct Strategy and exactly the policy equation used above. Positivity is vacuous for m=0. Applying this theorem to that supplied Strategy gives the stated original completion horizon and support; it needs no extra positivity premise after the Strategy and its exact policy equation are fixed. No injectivity, nonempty prototype family, unique route address, successful decoding or allowed prototype assumption is used.")),
            Paragraph(Text("The existing exact-trace compiler, support pruning and phase replay provide the same-source observer, first-occurrence cache and phase conclusions. Here the horizon measures the full logical request trace, including cache hits, and Qstar includes all literal route and prototype words. The estimate supplies neither a competitor minimum nor the full exact-compiler minimum, and it does not price address serialization, physical storage or an external prototype read port."))
        )));
    private static DocumentBlock Def(string n, string title, string prose) => Describe.Lean(
        DescribeId.Create("actual-completion-horizon-" + n.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + n), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula V(string s) => F.Id(s);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula And(params Formula[] fs) => Seq(fs.Select((f, i) =>
        i == 0 ? Par(f) : Seq(Sp, Land, Sp, Par(f))).ToArray());
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula Member(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula LeqOf(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula Pow(Formula a, Formula b) => Seq(a, Caret, Grp(b));
    private static Formula ContractFormula()
    {
        var horizon = Call("H", V("F"), V("p"), V("N"));
        var alphabet = Call("Qstar", V("F"), V("p"), V("N"));
        var trace = Call("trace", V("pi"), V("U"));
        var equality = All("U", V("Source"),
            EqOf(Call("terminal", V("pi"), V("U")),
                Call("outcome", V("F"), V("decode"), V("p"), V("U"))));
        var support = All("a", V("RawEntry"),
            Imp(Member(V("a"), trace), Member(Call("request", V("a")), alphabet)));
        var bounds = All("U", V("Source"), Imp(Call("Allowed", V("N"), V("U")),
            And(LeqOf(Call("length", trace), horizon), support)));
        var cardinal = Seq(D(1), Plus,
            Call("card", Call("allowedSources", V("N"))), Cdot,
            Par(Seq(horizon, Plus, D(1))), Cdot,
            Pow(D(2), Call("min", Call("card", alphabet), horizon)));
        var conclusion = And(equality, bounds,
            LeqOf(Call("stateCard", V("N"), V("pi")), cardinal));
        var assumptions = And(LeqOf(D(1), V("N")),
            EqOf(Call("policy", V("pi")),
                Call("normalizedPolicy", V("F"), V("decode"), V("p"))));
        return Disp(All("m", V("Nat"),
            All("F", Seq(Call("Fin", V("m")), Sp, To, Sp, V("Source")),
            All("decode", Seq(V("CoarseHistory"), Sp, To, Sp,
                Call("Option", Call("Fin", V("m")))),
            All("p", V("Route"), All("N", V("Nat"), All("pi", V("Strategy"),
                Imp(assumptions, conclusion))))))));
    }
    private static Formula Par(Formula f) => Seq(Open, f, Close);
}
