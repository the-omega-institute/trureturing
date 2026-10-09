using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class ActualPureAcquisitionCompilerDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite original observer preserves pure acquisition on every bounded source, all-history coarse control, every nominal cache lift and the exact node-fee baseline.",
        H("Finite Pure Acquisition and Exact Node Baseline"),
        Blocks(
            Paragraph(Text("The source, address, four raw replies, coarse quotient, acquisition policy, acquisition trace, finiteDecision and nodes are the original actual-tree objects. Allowed N U is the exact original leaf-budget class. For every N at least one, pureObserver inhabits the existing Observer contract with no source argument. Its actual runs use the existing Run, ActualPrefix, Legal and Admissible relations. In formulas M(N,p) denotes pureObserver N p, Trace(U) denotes acquisitionTrace [] U, nodeSet(U) denotes (nodes U).toFinset, eZero denotes the initial configuration, kappaHist denotes kappa_hist, card denotes Fintype.card, and Joint denotes the original J_N. Natural cardinalities are cast to Real in the joint-price formula.")),
            Def("coarsePrefixes", "Finite coarse-prefix carrier", "All coarse prefixes of all original allowed source acquisition traces, including terminal prefixes."),
            Def("CoarseIndex", "Coarse-prefix index", "A CoarseIndex is a coarse prefix together with its membership witness."),
            Def("PureRow", "Nominal row", "A nominal row is a coarse-prefix index together with one complete compatible raw-cache lift."),
            Def("PureState", "Rows plus sink", "PureState is the nominal row carrier plus one absorbing sink."),
            Def("pureStateFintype", "Finite pure carrier", "The pure carrier has a finite type instance obtained from the finite source prefix union and compatible fibers."),
            Def("nominalCard", "Exact nominal cardinality", "Each installed coarse prefix has distinct addresses because the original trace is the nodes preorder without duplicates. Thus noneCount counts coarse-none first occurrences. Every compatible branch or absent lift contributes a separate nominal row, whether or not any source reaches it; the absorbing sink contributes one more. The exact sum, rather than an upper bound or a reachability quotient, is used for the state price.", NominalFormula()),
            Theorem("pureState_card", "Exact full carrier count", "The finite sigma carrier has exactly the compatible-fiber sum plus one sink. This exact count determines the nominal-state term of the joint price.", Disp(All("N", V("Nat"), EqOf(Call("card", Call("PureState", V("N"))), Call("nominalCard", V("N")))))),
            Theorem("trace_addresses", "Original preorder addresses", "For every original source U and address prefix u, mapping Sigma.fst over acquisitionTrace u U gives nodes U with u prepended to each address. Tree induction preserves the root, left and right preorder. At the root, its paid Finset is exactly (nodes U).toFinset; the addresses are duplicate-free."),
            Def("emptyRow", "Source-independent empty row", "For N at least one, the empty coarse prefix belongs to the carrier and its unique compatible cache is empty. The initial row depends only on N and its positivity proof, with no source, source size, oracle or externally readable history."),
            Def("rowDecoder", "Original raw cache decoder", "Decode the compatible raw lift of the installed row. Addresses are distinct at every nominal row, including every ghost row."),
            Def("rowOfHistory", "Exact history row", "A raw history whose coarse projection belongs to coarsePrefixes is packed without changing its raw reports. This constructor is used in the proof of actual execution; the runtime has no history input."),
            Def("pureAction", "Coarse-only installed action", "At a row with coarse prefix g, the action is acquisitionPolicy (encodeHistory g). The sink action is Halt(false). Raw cache lifts cannot influence this action. A faithful finite table installs these values at all nominal rows."),
            Def("appendRow", "Coarse-only row or sink selection", "After query q and raw report y, append (q,kappa y) to the coarse prefix. Membership of that new prefix alone selects a row or the sink. A selected row packs the exact original cacheUpdate, which preserves the first raw value on a repeated hit. No raw contradiction test selects a control branch. In this pure acquisition carrier every retained extension has a fresh address; a repeated query extension is outside the prefix carrier regardless of its raw report."),
            Def("pureTransition", "Total raw transition", "A query row takes appendRow; a halt row absorbs every raw response. The sink is absorbing. All four raw reply columns are defined at every installed row."),
            Def("pureObserver", "Original finite observer", "The complete original Observer uses the empty row, coarse-only action, total raw transition and exact decoder. Its decoded_nodup field holds on every nominal configuration."),
            Def("control", "Coarse control projection", "control returns the coarse-prefix index for a row and none for the sink. Raw cache lifts are forgotten."),
            Theorem("pure_all_history_factorization", "Unrestricted coarse factorization", "Induction on the original PairReach relation preserves equality of control for every pair of raw responses with equal kappa. Both action and row-versus-sink selection factor through this control. The frozen pairActionInvariant_iff_allHistoryFactorization criterion yields action factorization on all raw histories, including inconsistent reports, repeated or wrong address labels and reports after halt. No actual-source or cache-truth premise restricts this proof.", Disp(Budget(Call("FactorsThrough", Call("historyAction", M), V("kappaHist"))))),
            Theorem("pure_acquisition_run", "Exact original acquisition run", "For every allowed original U, execute_to_run converts the original acquisition execution into an original Run with exactly acquisitionTrace [] U and finiteDecision U. Actual prefixes fix encodeHistory representatives, and truthful cache replies reproduce the same original source report. No query-all bounded-address baseline is substituted.", RunFormula()),
            Theorem("pure_actual_prefix_cache", "Every actual prefix has the original cache", "Every actual prefix h is a prefix of the exact original trace. Its decoded cache is literally h and is truthful on the same U. Pure acquisition has no repeated actual address, so this literal prefix equals its ordered first-occurrence cache. The proof retains a remaining original execute continuation at every prefix; the sink is never reached on an allowed source. Truth is asserted on actual prefixes, not on arbitrary ghost rows.", CacheFormula()),
            Theorem("pure_admissible", "Complete bounded admissibility", "The original Admissible contract follows from empty initial cache, actual-prefix truth and exact cacheUpdate, original finiteDecision correctness, exact finite acquisition runs and the separate unrestricted factorization theorem.", Disp(Budget(Call("Admissible", V("N"), M)))),
            Theorem("pure_node_fee", "Exact actual-node fee", "Original fee_run and the exact paid address identity give Fee(M,tau,U) equal to the sum of tau over (nodes U).toFinset for every allowed source. This identity holds for arbitrary real address prices.", FeeFormula()),
            Def("nodeMax", "Attained original node maximum", "nodeMax N p tau is the finite sup over the exact allowedSources N of the sum of tau over each source's original nodes. Its domain is nonempty for N at least one."),
            Theorem("pure_joint_price", "Exact source38.10 baseline", "The original J_N of the compiled observer is c times its exact full nominal count plus nodeMax. An original allowed source attains that node maximum. Both statements hold for arbitrary real tau and c; later domination and cutoff arguments additionally require nonnegative tau and strictly positive c.", PriceFormula()),
            Def("lawfulPureTable", "Faithful lawful baseline table", "Every nominal query and cache address belongs to Q_N, established from original node geometry and the acquisition existence supplier. bounded_table_representation and representation_contract then provide a table with exactly card(PureState N) rows, initial label zero, complete raw transition and cache correspondence, exact actual Run and prefix correspondence, all-history semantics, and exact Fee and J_N. The table belongs to the existing lawfulTables at that full cardinality. No ghost row is removed."),
            Paragraph(Text("For nonnegative tau and positive c, the cutoff K=floor(B/c), with B=c*nominalCard(N)+nodeMax(N,p,tau), and the attained minimum over lawfulTables at positive cardinalities at most K remain separate unproved statements. They require baseline table membership below K, strict price domination above K, a nonempty finite table-price union, and coverage of all original competitors by absent normalization and table representation. The general routed and prototype compiler, the ordered-cache count and the raw-table numerical bound are also not established here.") )
        )));
    private static DocumentBlock Def(string n, string title, string prose, Formula? formula = null) => Describe.Lean(
        DescribeId.Create("actual-pure-compiler-" + n.Replace("_", "-").ToLowerInvariant()), DeclarationHandle.Create(Prefix + n),
        H(title), formula is null ? StatementSource.WithoutFormula() : StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static DocumentBlock Theorem(string n, string title, string prose, Formula? formula = null) => Describe.Lean(
        DescribeId.Create("actual-pure-compiler-" + n.Replace("_", "-").ToLowerInvariant()), DeclarationHandle.Create(Prefix + n),
        H(title), formula is null ? StatementSource.WithoutFormula() : StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula V(string s) => F.Id(s);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula And(params Formula[] fs) => Seq(fs.Select((f, i) => i == 0 ? Par(f) : Seq(Sp, Land, Sp, Par(f))).ToArray());
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula Some(string name, Formula type, Formula body) => Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula Budget(Formula body) => All("N", V("Nat"), All("p", Seq(D(1), Sp, Leq, Sp, V("N")), body));
    private static Formula M => Call("M", V("N"), V("p"));
    private static Formula Trace => Call("Trace", V("U"));
    private static Formula Prices => Seq(V("Address"), Sp, Rightarrow, Sp, V("Real"));
    private static Formula NodeSum => Seq(Sum, Underscore, Grp(Seq(V("q"), Sp, InMacro, Sp, Call("nodeSet", V("U")))), Sp, Call("tau", V("q")));
    private static Formula NominalFormula() => Disp(All("N", V("Nat"), EqOf(Call("nominalCard", V("N")),
        Seq(D(1), Plus, Sum, Underscore, Grp(Seq(V("g"), Sp, InMacro, Sp, Call("coarsePrefixes", V("N")))), Sp,
            D(2), Caret, Grp(Call("noneCount", V("g")))))));
    private static Formula RunFormula() => Disp(Budget(All("U", V("Source"), Imp(Call("Allowed", V("N"), V("U")),
        Some("f", Call("PureState", V("N")), Call("Run", M, V("U"), Call("eZero", M), Trace, V("f"), Call("finiteDecision", V("U"))))))));
    private static Formula CacheFormula() => Disp(Budget(All("U", V("Source"), All("e", Call("PureState", V("N")),
        All("h", V("RawHistory"), Imp(And(Call("Allowed", V("N"), V("U")), Call("ActualPrefix", M, V("U"), V("e"), V("h"))),
            And(Call("IsPrefix", V("h"), Trace), EqOf(Call("decoder", M, V("e")), V("h")), Call("CacheTruth", V("h"), V("U")))))))));
    private static Formula FeeFormula() => Disp(Budget(All("tau", Prices, All("U", V("Source"),
        Imp(Call("Allowed", V("N"), V("U")), EqOf(Call("Fee", M, V("tau"), V("U")), NodeSum))))));
    private static Formula PriceFormula() => Disp(Budget(All("tau", Prices, All("c", V("Real"), And(
        EqOf(Call("Joint", V("N"), M, V("tau"), V("c")), Seq(V("c"), Sp, Cdot, Sp, Call("nominalCard", V("N")), Plus, Call("nodeMax", V("N"), V("p"), V("tau")))),
        Some("U", V("Source"), And(Call("Allowed", V("N"), V("U")), EqOf(Call("nodeMax", V("N"), V("p"), V("tau")), NodeSum))))))));
}
