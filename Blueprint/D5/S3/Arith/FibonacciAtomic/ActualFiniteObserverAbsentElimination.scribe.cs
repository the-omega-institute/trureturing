using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class ActualFiniteObserverAbsentEliminationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete finite nominal observers retain the original raw semantics; every address beyond the native leaf budget is absent, also on truthful cache hits.",
        H("Native Finite Observer and Bounded Raw Absence"),
        Blocks(
            Def("RawHistory", "Ordered raw reports", "Histories are chronological literal-address and four-response pairs. Order and repetitions remain. The source is the original nonempty FreeMagma Bool, addresses are List Bool, and positivity is membership in the third native substitution image."),
            Def("Allowed", "Original bounded sources", "Allowed(N,U) means that the native source has at most N leaves. This domain retains every original shape and label."),
            Def("Q_N", "Bounded node addresses", "Q_N contains exactly the words of length at most N minus one. Every literal word remains an original legal request."),
            Def("CacheTruth", "Same-source cache truth", "Every stored raw report agrees with readout at its literal address in the same immutable source."),
            Def("queryReply", "Truthful hits and source misses", "An exact address hit returns its stored raw report. Only an address miss reads the original source."),
            Def("cacheUpdate", "First-occurrence update", "A hit preserves the entire ordered cache. A miss appends exactly the queried address and raw response; it neither infers nor overwrites entries."),
            Def("Observer", "Complete nominal rows", "For any finite carrier E, the observer has a source-independent initial row e0, action, four-response transition and ordered raw cache decoder. The initial row witnesses nonemptiness. Decoded addresses have no duplicates at every nominal row, including unreachable rows. The finite carrier contains every dynamic distinction."),
            Def("barStep", "Absorbing response step", "A query row takes its raw-response transition. A halt row remains fixed for every raw response, independently of its transition table."),
            Def("responseState", "Response-word action", "Fold the absorbing step over the raw reply word from an arbitrary nominal row."),
            Def("historyState", "All-history state", "Fold only the raw responses from e0. Reported address labels are ignored even on impossible, inconsistent or unreachable histories."),
            Def("historyAction", "All-history action", "Return the action of the final absorbing row after the complete response fold."),
            Def("ActualPrefix", "Actual external trace prefixes", "An actual prefix begins at e0 and extends by the row's literal query and its hit-or-miss raw reply. The trace is an external record and supplies no additional controller memory."),
            Def("Run", "Sourcewise finite runs", "A finite inductive run follows those exact query transitions until an original halt, retaining every repeat and hit in order. No uniform fuel, clock, jump log or acyclic-row restriction is assumed."),
            Def("Legal", "Actual cache premises", "The initial decoded cache is empty. At every actual prefix its entries are true of the same source and each query successor decodes to exactly the first-occurrence update. Truth and update are not imposed on arbitrary counterfactual rows."),
            Def("Admissible", "Original complete bounded contract", "N is at least one. On every allowed source the observer is legal and has a finite run returning true exactly for the original third-substitution Positive target. Its action factors through the existing coarse history map on all finite histories. Nominal states are retained in full; no source port or canonical controller is installed."),
            Describe.Lean(DescribeId.Create("finite-observer-truthful-query-reply"), DeclarationHandle.Create(Prefix + "queryReply_eq_readout"),
                H("Truthful raw cache replies equal source readout"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every truthful raw cache on U and every literal address q, queryReply cache q U equals readout q U. A miss uses source readout by definition; an exact hit has that same raw value by CacheTruth. No coarse quotient replaces the cached reply."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("finite-observer-actual-prefix-semantics"), DeclarationHandle.Create(Prefix + "actualPrefix_semantics"),
                H("Actual prefixes realize folds and exact raw caches"), StatementSource.FromAuthor(PrefixSemanticsFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a legal observer on a fixed original source, every actual prefix ends at the row obtained by folding its raw replies with absorbing barStep. The decoded cache equals the chronological fold of cacheUpdate from the empty list, so repeated addresses retain their first entry and new addresses append in order. Every report in the external trace is true of that same source. Induction over chronological prefix extension uses the exact decoded-cache update law; an exact hit is true by cache truth and a miss is the original source readout."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("finite-observer-run-prefix-extension"), DeclarationHandle.Create(Prefix + "run_from_actualPrefix"),
                H("Head and tail runs extend chronological prefixes"), StatementSource.FromAuthor(RunExtensionFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A run from the row of any existing actual prefix extends that prefix by its entire ordered trace and ends at a halt row with its stated output bit. Induction on the run appends each current report to the prefix before extending through the tail; list append associativity aligns this chronological construction with head and tail execution. No legality or termination bound is needed for this correspondence."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("finite-observer-run-deterministic"), DeclarationHandle.Create(Prefix + "run_deterministic"),
                H("Unique finite trace, final row and output"), StatementSource.FromAuthor(DeterminismFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Any two finite runs from the same nominal row on the same immutable original source have equal traces, final rows and output bits. Induction on one run compares the other run's first constructor. Query and halt actions cannot coincide; two query actions have the same literal address and therefore the same decoded-cache reply and successor. The tail induction then gives equality of the complete ordered traces and outputs."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("finite-observer-admissible-run-contract"), DeclarationHandle.Create(Prefix + "admissible_run_contract"),
                H("Every admissible actual run has the original semantics"), StatementSource.FromAuthor(RunContractFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every original allowed source and every run from e0 of an admissible observer, the final row is an actual prefix row and is exactly historyState of the run trace. Its action and historyAction both halt with the run's bit. Its decoded cache is exactly the first-occurrence cacheUpdate fold from the empty list, and both this cache and every external trace report are true of the same original source. The output is true exactly for Positive of that source. Run extension and actual-prefix semantics establish the trace and cache conclusions. Admissible supplies existence of a correct run; finite-run uniqueness transfers its correct bit to the arbitrary run under consideration. No correspondence or correctness premise for that particular run is assumed."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("finite-observer-subtree-leaf-count"), DeclarationHandle.Create(Prefix + "subtree_leaf_count"),
                H("Native subtree leaf-count geometry"), StatementSource.FromAuthor(GeometryFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every edge on a native subtree path leaves a nonempty sibling subtree. Induction on the original FreeMagma tree bounds address length plus retained subtree leaf count by the original leaf count."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("finite-observer-outside-raw-absence"), DeclarationHandle.Create(Prefix + "outside_Q_N_absent"),
                H("Raw absence beyond the budget, including cache hits"), StatementSource.FromAuthor(AbsenceFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every allowed original source and every word outside Q_N, the subtree is missing: otherwise its positive leaf count contradicts the native path bound. The existing readout/subtree supplier then yields raw absent. A truthful ordered cache returns that same raw absent on a miss or a hit, and every stored entry at that address is raw absent."))), DescribeRole.Theorem))));

    private static DocumentBlock Def(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("finite-observer-" + name.ToLowerInvariant().Replace('_', '-')), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula V(string s) => F.Id(s);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Par(a), Sp, Land, Sp, Par(b));
    private static Formula All(string names, Formula type, Formula f) => Seq(Forall, Sp,
        Seq(names.Split(',').Select((name, i) => i == 0 ? V(name) : Seq(Comma, Sp, V(name))).ToArray()),
        Colon, Sp, type, Comma, Sp, Par(f));
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula Observers(Formula f) => All("E", V("Type"),
        Seq(OpenBracket, Call("Fintype", V("E")), CloseBracket, Comma, Sp,
            All("M", Call("Observer", V("E")), f)));
    private static Formula Report => Call("Sigma", Call("const", V("Address"), V("Reply")));
    private static Formula Replay(Formula trace)
    {
        Formula update = Call("cacheUpdate", V("cache"), Call("fst", V("a")), Call("snd", V("a")));
        Formula entryFunction = Par(Seq(V("a"), Colon, Sp, Report, Sp, Mapsto, Sp, update));
        Formula foldFunction = Par(Seq(V("cache"), Colon, Sp, V("RawHistory"), Sp, Mapsto, Sp, entryFunction));
        return Call("foldl", foldFunction, Seq(OpenBracket, CloseBracket), trace);
    }
    private static Formula PrefixSemanticsFormula()
    {
        Formula premise = And(Call("Legal", V("M"), V("U")), Call("ActualPrefix", V("M"), V("U"), V("e"), V("h")));
        Formula result = And(EqOf(Call("historyState", V("M"), V("h")), V("e")),
            And(EqOf(Call("decoder", V("M"), V("e")), Replay(V("h"))), Call("CacheTruth", V("h"), V("U"))));
        return Disp(Observers(All("U", V("Source"), All("e", V("E"), All("h", V("RawHistory"), Imp(premise, result))))));
    }
    private static Formula RunExtensionFormula()
    {
        Formula run = Call("Run", V("M"), V("U"), V("e"), V("t"), V("f"), V("b"));
        Formula prefix = Call("ActualPrefix", V("M"), V("U"), V("e"), V("h"));
        Formula result = And(Call("ActualPrefix", V("M"), V("U"), V("f"), Call("append", V("h"), V("t"))),
            EqOf(Call("action", V("M"), V("f")), Call("inr", V("b"))));
        return Disp(Observers(All("U", V("Source"), All("e,f", V("E"), All("t,h", V("RawHistory"),
            All("b", V("Bool"), Imp(And(run, prefix), result)))))));
    }
    private static Formula DeterminismFormula()
    {
        Formula left = Call("Run", V("M"), V("U"), V("e"), V("t"), V("f"), V("b"));
        Formula right = Call("Run", V("M"), V("U"), V("e"), V("s"), V("g"), V("c"));
        Formula result = And(EqOf(V("t"), V("s")), And(EqOf(V("f"), V("g")), EqOf(V("b"), V("c"))));
        return Disp(Observers(All("U", V("Source"), All("e,f,g", V("E"), All("t,s", V("RawHistory"),
            All("b,c", V("Bool"), Imp(And(left, right), result)))))));
    }
    private static Formula RunContractFormula()
    {
        Formula initial = Call("e0", V("M"));
        Formula premise = And(Call("Admissible", V("N"), V("M")),
            And(Call("Allowed", V("N"), V("U")), Call("Run", V("M"), V("U"), initial, V("t"), V("f"), V("b"))));
        Formula halt = Call("inr", V("b"));
        Formula correct = Seq(Par(EqOf(V("b"), V("true"))), Sp, Iff, Sp, Par(Call("Positive", V("U"))));
        Formula result = And(Call("ActualPrefix", V("M"), V("U"), V("f"), V("t")),
            And(EqOf(Call("historyState", V("M"), V("t")), V("f")),
            And(EqOf(Call("action", V("M"), V("f")), halt),
            And(EqOf(Call("historyAction", V("M"), V("t")), halt),
            And(EqOf(Call("decoder", V("M"), V("f")), Replay(V("t"))),
            And(Call("CacheTruth", Call("decoder", V("M"), V("f")), V("U")),
            And(Call("CacheTruth", V("t"), V("U")), correct)))))));
        return Disp(All("N", V("Nat"), Observers(All("U", V("Source"), All("t", V("RawHistory"),
            All("f", V("E"), All("b", V("Bool"), Imp(premise, result))))))));
    }
    private static Formula GeometryFormula() => Disp(All("U,T", V("Source"), All("q", V("Address"), Imp(
        EqOf(Call("subtree", V("q"), V("U")), Call("some", V("T"))),
        Seq(Call("length", V("q")), Plus, Call("length", V("T")), Sp, Le, Sp, Call("length", V("U")))))));
    private static Formula AbsenceFormula()
    {
        Formula absent = V("absent"), q = V("q"), u = V("U"), c = V("cache"), a = V("a");
        Formula report = Call("Sigma", Call("const", V("Address"), V("Reply")));
        Formula hit = All("a", report, Imp(And(Call("member", a, c), EqOf(Call("fst", a), q)), EqOf(Call("snd", a), absent)));
        Formula budget = Seq(V("Q"), Underscore, Grp(V("N")));
        return Disp(All("N", V("Nat"), All("U", V("Source"), All("q", V("Address"),
            Imp(And(Call("Allowed", V("N"), u), Seq(Neg, Sp, Call("member", q, budget))),
                And(EqOf(Call("readout", q, u), absent), All("cache", V("RawHistory"),
                    Imp(Call("CacheTruth", c, u),
                        And(EqOf(Call("queryReply", c, q, u), absent), hit)))))))));
    }
}
