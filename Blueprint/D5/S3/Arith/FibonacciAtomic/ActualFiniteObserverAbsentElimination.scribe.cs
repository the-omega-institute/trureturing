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
    private static Formula All(string names, Formula f) => Seq(Forall, Sp,
        Seq(names.Split(',').Select((name, i) => i == 0 ? V(name) : Seq(Comma, Sp, V(name))).ToArray()),
        Comma, Sp, Par(f));
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula GeometryFormula() => Disp(All("U,q,T", Imp(
        EqOf(Call("subtree", V("q"), V("U")), Call("some", V("T"))),
        Seq(Call("length", V("q")), Plus, Call("length", V("T")), Sp, Le, Sp, Call("length", V("U"))))));
    private static Formula AbsenceFormula()
    {
        Formula absent = V("absent"), q = V("q"), u = V("U"), c = V("cache"), a = V("a");
        Formula hit = All("a", Imp(And(Call("member", a, c), EqOf(Call("fst", a), q)), EqOf(Call("snd", a), absent)));
        Formula budget = Seq(V("Q"), Underscore, Grp(V("N")));
        return Disp(All("N,U,q", Imp(And(Call("Allowed", V("N"), u), Seq(Neg, Call("member", q, budget))),
            And(EqOf(Call("readout", q, u), absent), All("cache", Imp(Call("CacheTruth", c, u),
                And(EqOf(Call("queryReply", c, q, u), absent), hit)))))));
    }
}
