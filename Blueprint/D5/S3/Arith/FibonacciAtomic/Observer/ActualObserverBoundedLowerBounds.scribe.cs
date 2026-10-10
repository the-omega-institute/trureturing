using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;

internal sealed class ActualObserverBoundedLowerBoundsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverBoundedLowerBounds.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Correctness on the original bounded source domain forces complete positive leaf acquisition, an exact decoded cache spectrum, and lower bounds on the full nominal observer carrier.",
        H("Bounded Native Cache and Control Lower Bounds"),
        Blocks(
            Paragraph(Text("A source is an original nonempty ordered FreeMagma Bool tree. Allowed(N,U) means that its leaf count is at most N. Positive(U) means membership in the third iterate of the original substitution. An Observer has a finite complete nominal carrier E, initial row e0, source-independent actions and raw-response transitions, and a decoder whose cache addresses are distinct. Admissible(N,M) includes N at least one, correct finite termination for every original allowed source, exact truthful cache updates at every actual prefix, and coarse action factorization on all finite histories. Every finite Boolean word remains a permitted query, including absent addresses of arbitrary length.")),
            Definition("cachedVisits", "Decoded chronological prefix values", "cachedVisits(M,t) is the image of all indices from zero through length(t) under i mapped to decoder(historyState(M,t.take(i))). The external trace retains each literal address, raw reply and repetition. The observer receives only its current row and a raw response. Actual-prefix certificates identify these response folds with the actual configurations, including the initial empty cache and the terminal cache."),
            Definition("positiveSources", "Positive original bounded sources", "positiveSources(N) filters the exact allowedSources(N) enumeration by Positive. It counts distinct original trees, with every ordered shape and both labels, without identifying sources having the same partial observation. Write p_N for its cardinality."),
            Describe.Lean(DescribeId.Create("bounded-native-prefix-cache-spectrum"),
                DeclarationHandle.Create(Prefix + "prefix_cache_spectrum"),
                H("Exact actual-prefix cache spectrum"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For every M,U with Legal(M,U), every actual state e and raw prefix h, paid(decoder(M,e)) equals paid(h), card(cachedVisits(M,h)) equals card(paid(h))+1, and every cache in cachedVisits has paid support contained in paid(h). Repeats retain the ordered cache; each fresh address creates one distinct decoder value. The scope includes the empty prefix and terminal cache."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("bounded-native-cache-control-lower-bounds"),
                DeclarationHandle.Create(Prefix + "bounded_cache_control_lower_bounds"),
                H("Complete bounded-source lower bounds"),
                StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every positive allowed U and every native initial Run with trace t, all leaves of U belong to paid(t), the finite set of distinct literal requested addresses. The full nominal carrier satisfies length(U)+1 at most card(E). For every real address price tau that is nonnegative at every address, the leaf sum is at most Fee(M,tau,U) on that same U. Zero prices are permitted. All nominal rows, including unreachable rows, contribute to card(E).")),
                    Paragraph(Text("For every allowed U and every actual terminating Run, paid(decoder(f)) equals paid(t). Exactly card(paid(t))+1 distinct decoded caches occur along its chronological prefixes, and each prefix fold has an ActualPrefix certificate. Repeated requests can change the row but preserve the full cache. Each first acquisition appends one truthful raw entry and creates a new cache value. Thus k distinct acquired addresses give exactly k+1 cache values, including empty and terminal values; absent addresses also count.")),
                    Paragraph(Text("If p_N is positive, card(E) is at least p_N+2. Different positive sources require different true terminal rows: a shared decoder is truthful for both sources, contains all labelled leaves of the first, and the original leaf rigidity forces the sources to agree. A negative singleton requires a separate false terminal row. Since both answers occur, the source-independent initial row cannot halt and supplies a further row. The positive-count condition is essential; the one- and two-leaf domains contain no positive source.")),
                    Paragraph(Text("To force a positive leaf request, flip an omitted leaf. The flip preserves the original leaf budget and is negative. All paid source readouts agree, so induction on the native Run replays the exact ordered trace, final nominal row and output bit. Bounded correctness then contradicts the opposite source truth values. This argument uses no all-source Strategy. Induction on actual prefixes proves cache separation using the exact hit-or-append law. Finite image cardinality and nonnegative sum domination give the state and fee bounds.")),
                    Paragraph(Text("The conclusions concern decoded caches and nominal finite control, not physical memory, runtime, communication or table-description cost. They establish no minimum joint price, price cutoff or gamma formula."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Definition(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("bounded-native-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula V(string name) => F.Id(name);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula And(params Formula[] fs) => Seq(fs.Select((f, i) =>
        i == 0 ? Par(f) : Seq(Sp, Land, Sp, Par(f))).ToArray());
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula All(string names, Formula type, Formula body) => Seq(Forall, Sp,
        Seq(names.Split(',').Select((n, i) => i == 0 ? V(n) : Seq(Comma, Sp, V(n))).ToArray()),
        Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Le(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula Card(Formula f) => Call("card", f);
    private static Formula Paid(Formula f) => Call("paid", f);
    private static Formula Run => Call("Run", V("M"), V("U"), Call("e0", V("M")), V("t"), V("f"), V("b"));
    private static Formula Runs(Formula body) => All("t", V("RawHistory"),
        All("f", V("E"), All("b", V("Bool"), Imp(Run, body))));
    private static Formula Statement()
    {
        Formula leafSet = Call("toFinset", Call("leaves", V("U")));
        Formula leafSum = Seq(Sum, Underscore, Grp(Seq(V("q"), Sp, InMacro, Sp, leafSet)),
            Sp, Call("tau", V("q")));
        Formula nonnegative = All("q", V("Address"), Le(D(0), Call("tau", V("q"))));
        Formula positive = All("U", V("Source"), Imp(And(Call("Allowed", V("N"), V("U")),
            Call("Positive", V("U"))), Runs(And(Seq(leafSet, Sp, Subseteq, Sp, Paid(V("t"))),
                Le(Seq(Call("length", V("U")), Plus, D(1)), Card(V("E"))),
                All("tau", Seq(V("Address"), Sp, To, Sp, Mathbb, Grp(V("R"))),
                    Imp(nonnegative, Le(leafSum, Call("Fee", V("M"), V("tau"), V("U")))))))));
        Formula prefixes = All("i", V("Nat"), Imp(Le(V("i"), Call("length", V("t"))),
            Call("ActualPrefix", V("M"), V("U"),
                Call("historyState", V("M"), Call("take", V("t"), V("i"))),
                Call("take", V("t"), V("i")))));
        Formula caches = All("U", V("Source"), Imp(Call("Allowed", V("N"), V("U")), Runs(And(
            EqOf(Paid(Call("decoder", V("M"), V("f"))), Paid(V("t"))),
            EqOf(Card(Call("cachedVisits", V("M"), V("t"))), Seq(Card(Paid(V("t"))), Plus, D(1))),
            prefixes))));
        Formula count = Imp(Seq(D(0), Sp, Lt, Sp, Card(Call("positiveSources", V("N")))),
            Le(Seq(Card(Call("positiveSources", V("N"))), Plus, D(2)), Card(V("E"))));
        return Disp(All("E", V("Type"), Seq(OpenBracket, Call("Fintype", V("E")), CloseBracket,
            Comma, Sp, All("N", V("Nat"), All("M", Call("Observer", V("E")),
                Imp(Call("Admissible", V("N"), V("M")), And(positive, caches, count)))))));
    }
}
