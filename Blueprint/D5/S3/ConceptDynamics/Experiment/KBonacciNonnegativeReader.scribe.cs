using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Experiment;

internal sealed class KBonacciNonnegativeReaderDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Experiment/KBonacciNonnegativeReader.complete_source_8_2";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every globally correct, pointwise terminating deterministic actual-window protocol "
            + "with an unknown nonnegative nonzero fixed reader needs at least two preparations "
            + "in the worst case in dimension two.",
        H("Nonnegative Fixed Readers and the One-Preparation Obstruction"),
        Blocks(Describe.Lean(
            DescribeId.Create("complete-two-dimensional-preparation-obstruction"),
            DeclarationHandle.Create(Declaration),
            H("Unrestricted actual-history preparation lower bound"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "C denotes all worlds consisting of a strictly positive real two-vector c "
                        + "and a nonnegative real two-vector ell whose coordinate sum is positive. "
                        + "Both vectors and the location of any zero reader coordinate are unknown. "
                        + "The target is the original outer product c ell-transpose. Every "
                        + "preparation supplies exactly the same c within that world, with ell "
                        + "fixed across all successive runs. D is the exact initial scalar ell dot c.")),
                Paragraph(Text(
                    "A window b is a literal Boolean word of length three accepted from state zero "
                        + "by the original live-tail automaton. This is internal exclusion of two "
                        + "consecutive ones, rather than a requirement that every current tail "
                        + "survive. A(b) is its actual live evaluation matrix. For p and t in Fin 2, "
                        + "E(p,t) has entry one at (i,s) exactly when i=t and s+p<2. The first "
                        + "two conjuncts give the leading-endpoint correspondence for every actual "
                        + "legal window and actual realization of all four endpoint pairs.")),
                Paragraph(Text(
                    "Proto contains arbitrary deterministic full-history choice, stopping and "
                        + "matrix-output functions. Each recorded event retains its literal action, "
                        + "the preceding action list and its exact real read. The redundant prefix "
                        + "is checked against the actual history. A window requires a previously "
                        + "prepared object. A preparation discards the old object; a window acts "
                        + "only on the current one. There is no operation for returning to an old "
                        + "object, copying, resetting it, observing internally or obtaining a free read.")),
                Paragraph(Text(
                    "Every preparation immediately incurs its initial read, even in an empty run. "
                        + "Every complete window immediately incurs one read, including a killed "
                        + "object, a zero state and each repeated zero response. P, W and N count "
                        + "preparations, windows and paid reads in the actual terminal history. "
                        + "The protocol supplies a finite actual terminal execution separately on "
                        + "every world. No common fuel, window or read bound, continuity, "
                        + "measurability or computability hypothesis is imposed. Correct means "
                        + "that every actual terminal output equals the original outer product.")),
                Paragraph(Text(
                    "B(pi) is the supremum over C of the natural preparation count, embedded in "
                        + "the extended nonnegative reals. V is the infimum of B over all correct "
                        + "protocols in Proto. These complete-order operations allow positive "
                        + "infinity, and the empty correct-protocol class has infimum infinity. "
                        + "The displayed conjunction includes the positive paid initial read, "
                        + "the exact accounting identity, impossibility of one preparation "
                        + "everywhere, both extended-order lower bounds, failure of V=1 and "
                        + "failure of the same-protocol simultaneous budgets P<=1, W<=2, N<=3.")),
                Paragraph(Text(
                    "For the collision, stop before preparation or immediately after an initial "
                        + "read equal to one cannot separate the source's unequal target pairs. "
                        + "Otherwise the actual first word is selected from that same history. "
                        + "For leading endpoint one, use initial objects (1,1) and (1,2) with "
                        + "reader (1,0). For leading endpoint zero, use (1/4,3/4) and (3/4,1/4) "
                        + "with reader (1,1). In each case the initial reads agree, the reader is "
                        + "identical, and the selected actual window makes the objects identical, "
                        + "while their original outer products differ. Both trailing endpoints "
                        + "are included, including a zero first-window read.")),
                Paragraph(Text(
                    "The one-preparation assumption excludes every later preparation. Induction "
                        + "on the actual finite remaining history shows equal objects and equal "
                        + "fixed-reader responses after each selected window, including every "
                        + "zero state. The existing conditional execution-transfer theorem then "
                        + "replays that same terminal history on the second world. Execution "
                        + "monotonicity identifies its terminal output without a uniform "
                        + "termination assumption. Unequal targets contradict correctness.")),
                Paragraph(Text(
                    "This is the k=2 obstruction to extending the universal sharp resource law "
                        + "from strictly positive readers to all nonnegative nonzero readers. It "
                        + "excludes the preparation equality and the simultaneous same-protocol "
                        + "bounds. It establishes no exact optimal preparation, window or total "
                        + "read count on the enlarged domain, and does not separately refute "
                        + "a window-count or total-read infimum equality. The strictly positive "
                        + "reader results retain their original assumptions. The contract uses "
                        + "exact noiseless real reads and granted same-source preparations; no "
                        + "physical construction, noise tolerance or finite-precision claim follows."))),
            DescribeRole.Theorem))));

    private static Formula At(Formula f, params Formula[] args)
    {
        var parts = new List<Formula> { f, Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) parts.Add(Comma);
            parts.Add(args[i]);
        }
        parts.Add(Close);
        return Seq([.. parts]);
    }

    private static Formula All(Formula x, Formula type, Formula body) =>
        Seq(Open, Forall, Sp, x, Sp, InMacro, Sp, type, Comma, Sp, body, Close);

    private static Formula Statement()
    {
        Formula b = F.Id("b");
        Formula p = F.Id("p");
        Formula t = F.Id("t");
        Formula w = F.Id("w");
        Formula pi = F.Pi;
        Formula c = F.Id("C");
        Formula proto = F.Id("Proto");
        Formula window = F.Id("Window");
        Formula fin = At(F.Id("Fin"), D(2));
        Formula correct = At(F.Id("Correct"), pi);
        Formula prep = At(F.Id("P"), pi, w);
        Formula win = At(F.Id("W"), pi, w);
        Formula reads = At(F.Id("N"), pi, w);
        Formula budgets = Seq(prep, Le, D(1), Land, win, Le, D(2), Land, reads, Le, D(3));
        return Disp(Seq(
            All(b, window, Seq(Exists, Sp, p, Comma, t, InMacro, Sp, fin, Comma, Sp,
                At(F.Id("lead"), b), Eq, p, Land,
                At(F.Id("A"), b), Eq, At(F.Id("E"), p, t))), Land,
            All(p, fin, All(t, fin, Seq(Exists, Sp, b, InMacro, Sp, window, Comma, Sp,
                At(F.Id("A"), b), Eq, At(F.Id("E"), p, t)))), Land,
            All(w, c, Seq(D(0), Lt, At(F.Id("D"), w))), Land,
            All(pi, proto, All(w, c, Seq(reads, Eq, prep, Plus, win))), Land,
            All(pi, proto, Seq(correct, Implies, Neg,
                All(w, c, Seq(prep, Le, D(1))))), Land,
            All(pi, proto, Seq(correct, Implies, D(2), Le, At(F.Id("B"), pi))), Land,
            D(2), Le, F.Id("V"), Land, F.Id("V"), Neq, D(1), Land,
            Neg, Open, Exists, Sp, pi, InMacro, Sp, proto, Comma, Sp,
                correct, Land, All(w, c, budgets), Close));
    }
}
