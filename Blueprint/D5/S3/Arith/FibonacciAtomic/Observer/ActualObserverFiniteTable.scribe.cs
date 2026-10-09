using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;

internal sealed class ActualObserverFiniteTableDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverFiniteTable.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite native tables represent complete bounded observers and cover every admissible competitor after native absent normalization.",
        H("Faithful Finite Tables for Native Bounded Observers"),
        Blocks(
            Paragraph(Text("An observer carries every nominal configuration, including unreachable rows. Its action is a literal-word query or a Boolean halt; its transition has a column for each of the four original replies. Every nominal decoded cache has distinct addresses. Cache truth and the exact read, hit and append laws are required on actual executions. These two requirements have different scopes. In the displayed formulas Report denotes an original address and raw reply pair, while Q(N), eZero(M) and Joint(N,M,tau,k) denote Q_N N, M.e0 and J_N N M tau k, respectively.")),
            Def("BoundedAddress", "Finite literal words", "BoundedAddress N is the subtype of original Boolean words belonging to Q_N N, equivalently of length at most N minus one. Mathlib List.finite_length_le supplies finiteness directly. The representation retains the words themselves and their ordered bits."),
            Def("NativeCache", "Finite ordered raw cache decorations", "NativeCache N consists of lists of bounded literal words paired with original Reply values, with no repeated address. Finiteness follows by embedding these lists into Mathlib's finite type of duplicate-free lists over BoundedAddress N times Reply. Distinctness of addresses implies distinctness of pairs, but the reverse condition alone would permit two different reports at the same address and is insufficient."),
            Def("decodeCache", "Original ordered cache decoding", "decodeCache erases only the bounded-word membership proofs. It preserves literal words, raw alpha, beta, branch and absent values, and chronological first-hit order. Its address list is duplicate-free."),
            Def("NativeTable", "Complete finite tables", "NativeTable N n has an action in Sum (BoundedAddress N) Bool at every Fin n row, all four raw transition successors, and an ordered NativeCache decoration at every row. Its type is finite as a subtype of a finite product of function types. There is no reachability restriction or source-dependent initial label."),
            Def("tableObserver", "Interpretation in the original observer contract", "For a positive number n of rows, tableObserver assigns initial label zero, erases bounded-word proofs in the action column, retains the transition column, and decodes each cache decoration. It is an original Observer (Fin n). Absorbing halt semantics are supplied by the existing barStep; all installed nominal rows remain present."),
            Def("lawfulTables", "Exactly the admissible finite tables", "lawfulTables N n p filters the finite universal table set by Admissible N (tableObserver p T). This is the original contract: empty initial cache, raw cache truth and exact update at every actual prefix, correct finite termination on every original allowed source, and coarse action factorization on every raw history. The predicate is a mathematical specification; no effective real-price comparator or checker implementation is asserted."),
            Def("relabel", "Relabeling the whole nominal carrier", "For any equivalence r from E to Fin n, relabel M r transports the initial configuration and every raw successor through r, and pulls actions and decoded caches back through its inverse. No row is removed or merged."),
            Describe.Lean(DescribeId.Create("native-observer-bounded-table-representation"),
                DeclarationHandle.Create(Prefix + "bounded_table_representation"),
                H("Exact representation of every bounded observer"),
                StatementSource.FromAuthor(RepresentationFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Suppose every query row of M uses Q_N N and every entry of every nominal cache uses Q_N N. No correctness, termination or price premise is needed. Enumerate the complete carrier using Mathlib Fintype.equivFin, then swap the image of the original initial configuration with zero. Install each bounded action, transported successor and packed original cache. Erasing the membership proofs recovers every original cache entry in order. The resulting native table observer equals the relabeled original observer as a complete record."))), DescribeRole.Theorem),
            Def("RepresentationContract", "Exact actual and all-history correspondence", "RepresentationContract records initial label zero; exact action, transition and decoded-cache correspondence at every nominal row; equivalence of actual prefixes and finite runs at every original source, arbitrary starting row and literal raw trace; equality of counterfactual actions and transported folded states on every raw history; exact sourcewise Fee and J_N for arbitrary real prices; and transport of Admissible. Histories include impossible, unreachable, inconsistent and wrong-address reports, as well as reports after halt. The finite-run equivalence gives equality of the complete terminating-trace predicates, so Fee equality follows even when a source has no terminating run. The price identity preserves the full carrier cardinality and the maximum over the same original allowed-source domain."),
            Describe.Lean(DescribeId.Create("native-observer-competitor-table-coverage"),
                DeclarationHandle.Create(Prefix + "admissible_competitor_table_coverage"),
                H("Actual coverage of every original admissible competitor"),
                StatementSource.FromAuthor(CoverageFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every original admissible bounded observer M, native absent normalization supplies H on exactly the same E. Its all-row request condition bounds the action column. Its decoder identity filters every nominal cache to Q_N N, including unreachable rows; the original Observer already requires address distinctness on every nominal row. Thus H satisfies both representation premises. The constructed table has exactly card E rows, initial label zero, and a RepresentationContract with H, and belongs to lawfulTables at that cardinality.")),
                    Paragraph(Text("Induction on actual runs and prefixes transports the same raw requests and reports under relabeling. The existing List.foldl_hom transports arbitrary response words from the conjugacy of the absorbing steps. This proves the representation contract and transports original admissibility. Normalization supplies ordered trace deletion and exact projected caches; relabeling thereafter changes only row labels. For every nonnegative literal address price, each sourcewise table fee is at most the fee of M, and the joint price is at most that of M for every strictly positive state price.")),
                    Paragraph(Text("The table family is finite for each fixed nominal cardinality and covers every normalized competitor of that cardinality by construction. A complete minimum over all cardinalities additionally requires an actual lawful pure-acquisition baseline, a finite cutoff derived from its attained joint price and positive state price, and the finite minimum over exactly the admissible tables below that cutoff. Neither a baseline nor that cutoff is a premise of this coverage theorem. Exact numerical cache and raw-table counts are separate counting statements."))), DescribeRole.Theorem))));

    private static DocumentBlock Def(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("native-observer-table-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula V(string s) => F.Id(s);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Le(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula Lt(Formula a, Formula b) => Seq(a, Sp, F.Lt, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Par(a), Sp, Land, Sp, Par(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula All(string names, Formula type, Formula f) => Seq(Forall, Sp,
        Seq(names.Split(',').Select((name, i) => i == 0 ? V(name) : Seq(Comma, Sp, V(name))).ToArray()), Colon, Sp, type, Comma, Sp, Par(f));
    private static Formula Some(string names, Formula type, Formula f) => Seq(Exists, Sp,
        Seq(names.Split(',').Select((name, i) => i == 0 ? V(name) : Seq(Comma, Sp, V(name))).ToArray()), Colon, Sp, type, Comma, Sp, Par(f));
    private static Formula Observers(Formula f) => All("E", V("Type"),
        Seq(OpenBracket, Call("Fintype", V("E")), CloseBracket, Comma, Sp,
            All("N", V("Nat"), All("M", Call("Observer", V("E")), f))));
    private static Formula Size => Call("card", V("E"));
    private static Formula Labels => Call("Fin", Size);
    private static Formula Table => Call("NativeTable", V("N"), Size);
    private static Formula Equivalence => Call("Equiv", V("E"), Labels);
    private static Formula Interpreted => Call("tableObserver", V("p"), V("T"));
    private static Formula RealPrices => Seq(V("Address"), Sp, Rightarrow, Sp, V("Real"));
    private static Formula Nonnegative => All("q", V("Address"), Le(D(0), Call("tau", V("q"))));

    private static Formula RepresentationFormula()
    {
        Formula requests = All("e", V("E"), All("q", V("Address"),
            Imp(EqOf(Call("action", V("M"), V("e")), Call("inl", V("q"))),
                Call("Member", V("q"), Call("Q", V("N"))))));
        Formula caches = All("e", V("E"), All("a", V("Report"),
            Imp(Call("Member", V("a"), Call("decoder", V("M"), V("e"))),
                Call("Member", Call("fst", V("a")), Call("Q", V("N"))))));
        Formula result = And(EqOf(Call("r", Call("eZero", V("M"))), D(0)),
            EqOf(Interpreted, Call("relabel", V("M"), V("r"))));
        return Disp(Observers(Imp(And(requests, caches), Some("p", Lt(D(0), Size),
            Some("r", Equivalence, Some("T", Table, result))))));
    }

    private static Formula CoverageFormula()
    {
        Formula sourceFees = All("U", V("Source"), Imp(Call("Allowed", V("N"), V("U")),
            Le(Call("Fee", Interpreted, V("tau"), V("U")), Call("Fee", V("M"), V("tau"), V("U")))));
        Formula joint = All("k", V("Real"), Imp(Lt(D(0), V("k")),
            Le(Call("Joint", V("N"), Interpreted, V("tau"), V("k")),
                Call("Joint", V("N"), V("M"), V("tau"), V("k")))));
        Formula prices = All("tau", RealPrices, Imp(Nonnegative, And(sourceFees, joint)));
        Formula contracts = And(Call("NormalizationContract", V("N"), V("M"), V("H")),
            And(Call("RepresentationContract", V("N"), V("H"), V("p"), V("r"), V("T")),
                And(Call("Member", V("T"), Call("lawfulTables", V("N"), Size, V("p"))), prices)));
        return Disp(Observers(Imp(Call("Admissible", V("N"), V("M")),
            Some("H", Call("Observer", V("E")), Some("p", Lt(D(0), Size),
                Some("r", Equivalence, Some("T", Table, contracts)))))));
    }
}
