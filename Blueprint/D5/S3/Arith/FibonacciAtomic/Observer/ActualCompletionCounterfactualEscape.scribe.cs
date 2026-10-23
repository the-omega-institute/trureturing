using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;

internal sealed class ActualCompletionCounterfactualEscapeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionCounterfactualEscape.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every original normalized completion has one matching prefix whose fresh acquisition branch ladder escapes each finite atomic-action Observer on raw counterfactual histories.",
        H("Native Counterfactual Completion Obstruction"),
        Blocks(
            Paragraph(Text("Address is the original list of Boolean directions; RawHistory retains literal addresses and raw Reply values, including branch, absent, contradictory repetitions and reports that no source realizes. Source is the original nonempty ordered FreeMagma Bool tree. The arbitrary finite family F may be empty or contain duplicates. The finite PassiveProtocol route and decoder are unrestricted.")),
            Definition("leftAddress", "Literal all-left address",
                Disp(All("n", V("Nat"), EqOf(Call("leftAddress", V("n")), Call("replicate", V("n"), V("false"))))),
                "leftAddress(n) is the literal Boolean word of n false directions, with empty root at zero. No quotient identifies words of different lengths."),
            Definition("branchHistory", "Chronological branch ladder",
                Disp(And(EqOf(Call("branchHistory", D(0)), Call("nil")),
                    All("n", V("Nat"), EqOf(Call("branchHistory", Seq(V("n"), Plus, D(1))),
                        Call("append", Call("branchHistory", V("n")),
                            Call("singleton", Call("pair", Call("leftAddress", V("n")), V("branch")))))))),
                "branchHistory(n) reports branch at depths zero through n minus one. These reports are formal raw inputs, with no bounded-source realization premise. The chosen ladder is fixed by encodeHistory after kappa_hist; arbitrary raw histories are not fixed. In particular a root absent report empties the raw frontier, whereas its coarse-none representative is branch and inserts both children."),
            Definition("queryAddressLength", "Length of every nominal atomic action",
                Disp(And(All("q", V("Address"), EqOf(Call("queryAddressLength", Call("inl", V("q"))), Call("length", V("q")))),
                    All("b", V("Bool"), EqOf(Call("queryAddressLength", Call("inr", V("b"))), D(0))))),
                "An atomic query action contributes its literal address length; either Boolean halt contributes zero. The finite maximum in the proof ranges over the complete nominal Observer carrier, including dormant query rows and absorbing halt rows."),
            Describe.Lean(DescribeId.Create("native-counterfactual-completion-escape"),
                DeclarationHandle.Create(Prefix + "counterfactual_escape"),
                H("One fresh prefix and an unbounded native ladder"),
                StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every m, F : Fin m to Source, decoder, finite route p and original Strategy pi with the displayed exact policy identity, the theorem constructs one finite raw prefix pre before quantifying either depth or Observer. Every prefix step has the literal matching-address certificate pi.policy(pre.take(k)) = inl((pre.get(k)).address). For every raw suffix s, the full original phase parser returns acquisition(kappa_hist(s)) and acquisitionPolicy(encodeHistory(kappa_hist(s))). In particular the local suffix at s empty is genuinely empty. Its action is pi.policy(pre ++ s) by the first conjunct of phase_replay_contract, applied to the original policy identity.")),
                    Paragraph(Text("A singleton source of false is used solely to choose answers along the arbitrary finite route. encode_projection identifies the resulting coarse route with its raw representative. Induction on the native PassiveProtocol proves matching at each chronological request, preserving the seen history and repeated addresses. If decode selects no prototype, the route itself is pre. If it selects i, the existing leaf-cardinality and labelled-leaf facts give a first leaf q with Boolean expectation. Append the matching-address branch report at q; its coarse none differs from that expectation. The existing first-verifier-mismatch reset yields fresh acquisition for every suffix, even if q was reported in the route. This construction adds no prototype and asserts no realization of the entire counterfactual history.")),
                    Paragraph(Text("The substantive new invariant is: for every n there exists rest with frontier(branchHistory(n)) = leftAddress(n) :: rest. Symbolic induction uses the original acquisitionStep: a matching head branch replaces the head with its left child followed by its right child and retains all pending addresses. Normalization fixes precisely this ladder, so the phase action identity yields pi.policy(pre ++ branchHistory(n)) = inl(leftAddress(n)). This invariant is used on the live path to the final disagreement.")),
                    Paragraph(Text("For every universe-polymorphic finite E and original Observer M, let B be the finite supremum of queryAddressLength(M.action(e)) over all e in E. Finset.le_sup bounds the actual history row by B. On the same prefix and ladder at n = B + 1, the strategy requests a word of length B + 1, so historyAction(M,pre ++ branchHistory(n)) differs. No assumption of existing disagreement, fallback reachability or infinite action range occurs in the telescope.")),
                    Paragraph(Text("This is the source-level implication of proposition 38.71. An original positive-family completion supplies pi and the exact policy identity through completion_contract; the structural proof uses neither prototype positivity nor a source budget. Thus for any positive allowed budget, including one or two, all-history equality with a finite Observer contradicts the displayed disagreement. These are direct applications, rather than additional retained mathematical declarations. The theorem retains impossible histories and arbitrary literal addresses; it does not replace all-history equality by actual-source equality or by coarse factorization.")),
                    Paragraph(Text("The actual bounded-source compiler of proposition 38.70 still reproduces actual traces, raw caches and stopping behavior on its promised sources. Its counterfactual behavior may differ from the original completion. A generic finite-state stream emitter with an external output accumulator can assemble words over several outputs; that accumulator and interface are outside this Observer model, in which each row emits one complete literal address or one Boolean halt. No physical memory, runtime or stream-transducer bound is asserted. The result is a native formalization and application of the source argument, without a literature originality claim."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Definition(string name, string title, Formula formula, string prose) => Describe.Lean(
        DescribeId.Create("native-counterfactual-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula V(string name) => F.Id(name);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula And(params Formula[] fs) => Seq(fs.Select((f, i) =>
        i == 0 ? Par(f) : Seq(Sp, Land, Sp, Par(f))).ToArray());
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Arr(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Policy(Formula h) => Call("policy", V("pi"), h);
    private static Formula Norm(Formula h) => Call("encodeHistory", Call("kappaHist", h));
    private static Formula Statement()
    {
        Formula history = Call("append", V("pre"), Call("branchHistory", V("n")));
        Formula matching = All("k", Call("Fin", Call("length", V("pre"))),
            EqOf(Policy(Call("take", V("pre"), Call("val", V("k")))),
                Call("inl", Call("fst", Call("get", V("pre"), V("k"))))));
        Formula fresh = All("s", V("RawHistory"),
            EqOf(Call("routePhase", V("F"), V("decode"), V("p"), Call("nil"),
                    Call("kappaHist", Call("append", V("pre"), V("s")))),
                Call("pair", Call("acquisition", Call("kappaHist", V("s"))),
                    Call("acquisitionPolicy", Norm(V("s"))))));
        Formula ladder = All("n", V("Nat"), EqOf(Policy(history), Call("inl", Call("leftAddress", V("n")))));
        Formula finite = All("E", Call("Type", V("u")), Seq(OpenBracket, Call("Fintype", V("E")), CloseBracket,
            Comma, Sp, All("M", Call("Observer", V("E")), Ex("n", V("Nat"),
                Seq(Call("historyAction", V("M"), history), Sp, Neq, Sp, Policy(history))))));
        Formula equation = EqOf(Call("policy", V("pi")), Seq(LambdaLower, Sp,
            V("h"), Colon, Sp, V("RawHistory"), Sp, Mapsto, Sp,
            Call("controllerPolicy", Call("compileRaw", V("F"), V("decode"), V("p"), Call("nil")), Norm(V("h")))));
        return Disp(All("u", V("Universe"), All("m", V("Nat"),
            All("F", Arr(Call("Fin", V("m")), V("Source")),
            All("decode", Arr(V("CoarseHistory"), Call("Option", Call("Fin", V("m")))),
            All("p", Call("PassiveProtocol", V("Address"), Call("constant", Call("Option", V("Bool")))),
            All("pi", V("Strategy"), Seq(Par(equation), Sp, Implies, Sp,
                Ex("pre", V("RawHistory"), And(matching, fresh, ladder, finite))))))))));
    }
}
