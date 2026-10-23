using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Patterns.Separable;

internal sealed class ActualCyclesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual least-cut cycles have exact finite-tuple probabilities and lose no mass under finite exhaustion.",
        H("Actual Complete Cycles"),
        Blocks(
            Paragraph(Text(
                "U(n) is the finite set of literal permutations of Fin(n) avoiding 2413 and 3142. "
                + "At a least direct or skew cut, a small left indecomposable factor is emitted; "
                + "a small right factor is removed and the forced cut sign alternates. A complete "
                + "cycle ends at the first left emission. It leaves an actual unrestricted "
                + "separable permutation, on which the next cycle is parsed.")),
            Paragraph(Text(
                "For natural K and H, Cycle(K,sign,H) contains right removals followed by one "
                + "left emission, with at most H steps and each removed or emitted shape of "
                + "length between 1 and K. The terminal shape has no proper cut of its sign. "
                + "Family(K,H) also records the initial sign. Tuple(K,H,k) records k complete "
                + "cycles, including the unique empty tuple for k=0. Its size is the sum of "
                + "all removed and emitted lengths. Every fixed finite sequence of these "
                + "nonempty shapes is represented once the two bounds are large enough.")),
            Paragraph(Text(
                "Write T(K,H,k)=k*H*K+max(2*K,1). For n>T, Event(tuple,n) is the actual "
                + "EndpointHistory.EventFor fiber, recursively restricted by the tuple event "
                + "on the true remaining permutation. Success is the union of these finite "
                + "tuple events. Failed is its literal complement for n>T and is the whole "
                + "source for n<=T. The probability functions are the real masses under the "
                + "uniform distribution on U(n), extended by zero below the threshold. "
                + "No unsuccessful restricted leaf is assigned the mass of its full leaf.")),
            Paragraph(Text(
                "In the statement, C=Tuple(K,H,k), T=T(K,H,k), s(c)=size(c), "
                + "A(c,n) is the actual tuple event, and p(c,n) is its zero-extended probability. "
                + "P(K,H,k,n) is the zero-extended success probability and F(K,H,k,n) "
                + "is the actual failed event. An n>T quantifier includes its threshold guard. "
                + "Size, bound and cycle-count variables range over natural numbers, epsilon "
                + "ranges over the reals, and limits use the full sequence of natural n. "
                + "The function event(c,n) in the last clause is the original history event "
                + "for c in Family(K,H); FirstSuccess is the original classifier success kind.")),
            Describe.Lean(
                DescribeId.Create("actual-complete-cycle-tuples"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Patterns/Separable/ActualCycles.actual_complete_cycles"),
                H("Exact finite tuples and finite-complement exhaustion"),
                StatementSource.FromAuthor(Disp(FullStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every K,H,k,n with n>T(K,H,k), two tuple events containing the "
                        + "same actual permutation have equal tuples. The remaining size "
                        + "n-size(tuple) is positive. Each event has exactly "
                        + "card(U(n-size(tuple))) members and the displayed exact probability. "
                        + "For every fixed tuple its extended probability converges, along "
                        + "all natural n, to rho^size(tuple), where rho=(sqrt(2)-1)^2.")),
                    Paragraph(Text(
                        "The success event has cardinality equal to the sum, over all "
                        + "tuples, of card(U(n-size(tuple))). At every n the actual failed "
                        + "mass is 1 minus the extended success probability. For fixed "
                        + "K,H,k, the success probability converges to the finite sum of "
                        + "rho^size(tuple). For every fixed k and every real epsilon>0 "
                        + "there are K,H,N such that, for every n>=N, the actual failed "
                        + "mass is less than epsilon. An unbounded cycle type records arbitrary "
                        + "finite shapes before any cap is chosen. Every fixed tuple in that "
                        + "type has a finite bounded representation with the same shapes "
                        + "and a full-sequence probability limit rho raised to its total "
                        + "length. This includes k=0 and all empty "
                        + "finite families; all actual singleton conventions are retained.")),
                    Paragraph(Text(
                        "A first-cycle event exists exactly when the original actual minimum-cut "
                        + "classifier, with target 1 and label threshold 0, returns its good "
                        + "success kind. All other classifier kinds retain their original "
                        + "restricted actual fibers. Unique parsing follows from the "
                        + "existing stable least-cut fibers. "
                        + "The history reconstruction bijection identifies each tuple fiber "
                        + "with its true remaining U(n-size(tuple)). The actual fixed-shift "
                        + "count ratio gives its full-sequence limit. If u(K) is the partial "
                        + "critical mass of nonempty U-shapes and j(K) that of the signed "
                        + "indecomposable shapes, the limiting tuple mass is "
                        + "(2*j(K)*sum(r<H,u(K)^r))^k. The shared actual-shape theorem gives "
                        + "u(K)->b and j(K)->(1-b)/2, with 0<b=sqrt(2)-1<1. First taking "
                        + "K large for fixed H, then H large, gives total mass one and "
                        + "hence the stated actual finite-complement bound.")),
                    Paragraph(Text(
                        "This theorem concerns finite actual permutation experiments. It "
                        + "does not construct a common infinite execution, identify all "
                        + "position or label observations, prove conditional endpoint marks "
                        + "or a predictable hazard, or supply discrepancy and occupation "
                        + "estimates for the absolute-discrepancy application."))),
                DescribeRole.Theorem))));

    private static StrataLint.Scribe.Formula V(string name) => F.Id(name);
    private static StrataLint.Scribe.Formula Part(StrataLint.Scribe.Formula body) =>
        Seq(Open, body, Close);
    private static StrataLint.Scribe.Formula All(
        StrataLint.Scribe.Formula variables, StrataLint.Scribe.Formula body) =>
        Part(Seq(Forall, Sp, variables, Comma, Sp, body));
    private static StrataLint.Scribe.Formula Common(StrataLint.Scribe.Formula body) =>
        All(Seq(V("K"), Comma, V("H"), Comma, V("k")), body);
    private static StrataLint.Scribe.Formula Members() => Seq(V("c"), InMacro, Sp, V("C"));
    private static StrataLint.Scribe.Formula Large() => Seq(V("n"), Gt, V("T"));
    private static StrataLint.Scribe.Formula Remaining() =>
        Call("U", Seq(V("n"), Minus, Call("s", V("c"))));
    private static StrataLint.Scribe.Formula Weight(StrataLint.Scribe.Formula c) =>
        Seq(V("rho"), Caret, Grp(Call("s", c)));
    private static StrataLint.Scribe.Formula Limit(StrataLint.Scribe.Formula expression) =>
        Seq(Lim, Underscore, Grp(V("n"), To, Infty), expression);
    private static StrataLint.Scribe.Formula Total(StrataLint.Scribe.Formula expression) =>
        Seq(Sum, Underscore, Grp(Members()), expression);
    private static StrataLint.Scribe.Formula SuccessProbability() =>
        Call("P", V("K"), V("H"), V("k"), V("n"));
    private static StrataLint.Scribe.Formula FailedEvent() =>
        Call("F", V("K"), V("H"), V("k"), V("n"));

    private static StrataLint.Scribe.Formula FullStatement() => Seq(
        Common(All(Large(), All(Seq(V("c"), Comma, V("d"), InMacro, Sp, V("C")),
            All(Seq(V("x"), InMacro, Sp, Call("U", V("n"))), Seq(
                Part(Seq(V("x"), InMacro, Sp, Call("A", V("c"), V("n")), Sp, Land, Sp,
                    V("x"), InMacro, Sp, Call("A", V("d"), V("n")))),
                Sp, Implies, Sp, V("c"), Eq, V("d")))))), Sp, Land, Sp,
        Common(All(Large(), All(Members(), Seq(
            D(0), Lt, V("n"), Minus, Call("s", V("c")), Sp, Land, Sp,
            Call("card", Call("A", V("c"), V("n"))), Eq, Call("card", Remaining()),
            Sp, Land, Sp, Call("Pr", Call("A", V("c"), V("n"))), Eq,
            Frac, Grp(Call("card", Remaining())), Grp(Call("card", Call("U", V("n")))))))),
        Sp, Land, Sp,
        Common(All(Members(), Seq(Limit(Call("p", V("c"), V("n"))), Eq, Weight(V("c"))))),
        Sp, Land, Sp,
        Common(All(Large(), Seq(Call("card", Call("Success", V("K"), V("H"), V("k"), V("n"))),
            Eq, Total(Call("card", Remaining()))))), Sp, Land, Sp,
        Common(All(V("n"), Seq(Call("Pr", FailedEvent()), Eq, D(1), Minus,
            SuccessProbability()))), Sp, Land, Sp,
        Common(Seq(Limit(SuccessProbability()), Eq, Total(Weight(V("c"))))), Sp, Land, Sp,
        All(V("k"), All(Seq(V("epsilon"), Gt, D(0)), Seq(
            Exists, Sp, V("K"), Comma, V("H"), Comma, V("N"), Comma, Sp,
            All(Seq(V("n"), Geq, Sp, V("N")), Seq(
                Call("Pr", FailedEvent()), Lt, V("epsilon")))))), Sp, Land, Sp,
        All(V("k"), All(Seq(V("c"), InMacro, Sp, Call("UnboundedTuple", V("k"))), Seq(
            Exists, Sp, V("K"), Comma, V("H"), Comma, Sp,
            Part(Seq(Exists, Sp, V("d"), InMacro, Sp,
                Call("Tuple", V("K"), V("H"), V("k")), Comma, Sp,
                Call("erase", V("d")), Eq, V("c"), Sp, Land, Sp,
                Limit(Call("p", V("d"), V("n"))), Eq, Weight(V("c"))))))), Sp, Land, Sp,
        All(Seq(V("K"), Comma, V("H")), All(Seq(V("n"), Gt,
            V("H"), Cdot, Sp, V("K"), Plus, Call("max", Seq(D(2), Cdot, Sp, V("K")), D(1))),
            All(Seq(V("x"), InMacro, Sp, Call("U", V("n"))), Seq(
                Part(Seq(Exists, Sp, V("c"), InMacro, Sp, Call("Family", V("K"), V("H")),
                    Comma, Sp, V("x"), InMacro, Sp, Call("event", V("c"), V("n")))),
                Sp, Iff, Sp, Call("FirstSuccess", V("K"), V("H"), V("n"), V("x")))))));
}
