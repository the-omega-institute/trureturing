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
            Describe.Lean(DescribeId.Create("native-observer-representation-contract"),
                DeclarationHandle.Create(Prefix + "representation_contract"),
                H("A faithful complete table satisfies the representation contract"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Given an equivalence r between the complete carrier and Fin(card E), a native table T with initial label zero, and equality of tableObserver with relabel M r, every field of RepresentationContract holds. The supplier preserves exact actions, four-reply successors, ordered caches, actual prefixes and runs, all raw-history semantics, arbitrary real Fee and J_N, and admissibility. It is consumed both by competitor coverage and by the lawful pure-acquisition baseline table."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-observer-competitor-table-coverage"),
                DeclarationHandle.Create(Prefix + "admissible_competitor_table_coverage"),
                H("Actual coverage of every original admissible competitor"),
                StatementSource.FromAuthor(CoverageFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every original admissible bounded observer M, native absent normalization supplies H on exactly the same E. Its all-row request condition bounds the action column. Its decoder identity filters every nominal cache to Q_N N, including unreachable rows; the original Observer already requires address distinctness on every nominal row. Thus H satisfies both representation premises. The constructed table has exactly card E rows, initial label zero, and a RepresentationContract with H, and belongs to lawfulTables at that cardinality.")),
                    Paragraph(Text("Induction on actual runs and prefixes transports the same raw requests and reports under relabeling. The existing List.foldl_hom transports arbitrary response words from the conjugacy of the absorbing steps. This proves the representation contract and transports original admissibility. Normalization supplies ordered trace deletion and exact projected caches; relabeling thereafter changes only row labels. For every nonnegative literal address price, each sourcewise table fee is at most the fee of M, and the joint price is at most that of M for every strictly positive state price.")),
                    Paragraph(Text("The table family is finite for each fixed nominal cardinality and covers every normalized competitor of that cardinality by construction. The complete joint-price application below uses this coverage conclusion, the existing pure-acquisition baseline and exact finite checks. Neither the baseline nor the price cutoff is a premise of the coverage theorem."))), DescribeRole.Theorem),
            Paragraph(Text("Fix N at least one, arbitrary real literal-address prices tau(q) at least zero and state price k strictly positive. All original competitors are the existing Observer E with arbitrary universe-polymorphic finite full nominal E and Admissible N M. Their queries may use every original word, and their raw caches and histories retain order, repeats and impossible reports. No all-source Strategy hypothesis is added. allowedSources_exact identifies the finite source enumeration with every original tree of leaf count at most N. Partitioning this class by leaf count j and alpha count a, the existing GenealogicalFiberTransport.result gives Cat(j-1) times choose(j,a) in each composition fiber; summing choose(j,a) gives d(N)=sum(j=1..N) Cat(j-1)*2^j. The list-to-tuple equivalence partitions literal bounded words by lengths zero through N-1; the finite geometric sum gives a(N)=2^N-1. The original subtree_leaf_count and outside_Q_N_absent supply node containment and raw absent outside that set. The bounded comb-leaf realization in source38.40 is context and is not needed as a premise of this optimization.")),
            Paragraph(Text("For a=card(BoundedAddress N), a chronological address-distinct cache of length j corresponds bijectively to an embedding Fin j into BoundedAddress N and an arbitrary function Fin j to the four original Reply values. The map is List.ofFn of the address/report pairs; its inverse reads the original list positions. No raw cache is discarded for being unreachable or untruthful on a source. Mathlib card_embedding_eq, card_fun, card_sigma and descFactorial_eq_div give exactly gamma(a)=sum(j=0..a) a!/(a-j)!*4^j. In particular gamma(0)=1, gamma(1)=5 and gamma(2)=41. NativeTable is exactly the product of its three full field functions. There are (a+2)^n action columns, (n^4)^n four-successor columns and gamma(a)^n cache columns. Thus its raw cardinality equals [(a+2)*n^4*gamma(a)]^n, which supplies the original upper bound. Halt successor junk remains in this raw enumeration and is absorbed by barStep.")),
            Paragraph(Text("The two acceptance checks stay separate. ActualObserverFiniteChecks.sourceCheck_iff characterizes the n-row source-orbit test without preassuming Legal: initial decoder empty, a correct finiteDecision halt before n, and raw truth and exact queryReply/cacheUpdate equality at every row of that orbit window, including the absorbing terminal row. Apply it to every allowedSources member. For the independent all-history check enumerate finite subsets R of the full E times E, accepting when R contains (e0,e0), is closed under every pair of raw replies with equal coarse image through the original absorbing barStep, and has equal actions at every member. Its acceptance predicate uses only finite row data. The frozen pairReach_iff_equal_coarse_response_words characterization and Mathlib List.rel_foldl propagate the closed certificate along equal-coarse words and prove soundness; completeness uses the generated finite pair set as a mathematical witness. PairReach is never an oracle in acceptance. The existing pairActionInvariant_iff_allHistoryFactorization converts this certificate exactly to all-history factorization. Combining the tests retains precisely lawfulTables, without a global acyclicity condition, cache-truth pruning of pairs or a coarse cache comparison.")),
            Paragraph(Text("Take the unchanged pureObserver N p. Its full nominal cardinality is s0=nominalCard N=1+sum(g in coarsePrefixes N)2^noneCount(g), including every compatible ghost cache lift and the absorbing sink. pure_node_fee charges exactly the same source actual nodes; pure_joint_price gives its achieved B=k*s0+nodeMax(N,p,tau), with an allowed original source attaining nodeMax. lawfulPureTable is a same-cardinality original native table with initial zero and the complete representation contract. Nonnegative sums give nodeMax at least zero and B strictly positive. Let K be the natural floor of B/k; nonnegativity makes this the same integer floor. Nat.le_floor gives s0 at most K. For every original observer with card E greater than K, Nat.floor_lt gives k*card E greater than B and fee nonnegativity gives J_N(M) greater than B.")),
            Paragraph(Text("Form the finite dependent pool of all pairs (n,T) with 1 at most n at most K and T in precisely lawfulTables N n. Price each candidate by its original J_N, preserving the maximum over the same original sources and each source chronological paid-address set. The pure table belongs to this pool and has price B, so the pool is nonempty. Finset.exists_min_image selects an actual table Tstar with the least pool price, at most B. For an arbitrary original admissible M, a carrier above K has price greater than B. Otherwise admissible_competitor_table_coverage supplies a lawful table at exactly card E whose price is at most J_N(M); pool minimality then gives J_N(Tstar) at most J_N(M). Tstar is itself an original admissible observer. The minimum therefore is attained in the original class, not only in a representation of candidate costs.")),
            Paragraph(Text("The unrestricted price set consists of all real J_N values of arbitrary original admissible Observer(Fin n), for every positive natural n, with unrestricted word actions and raw caches before normalization. Every arbitrary finite original E has exactly its price in this set by full-carrier relabel, relabel_admissible and relabel_fee; no reachable-state quotient or bounded catalogue defines this set. The selected Tstar belongs to it and lower-bounds it. IsLeast.csInf_eq proves that its literal real sInf equals the min of the finite lawful pool price image. The simultaneous universal inequality over every E:Type u makes the carrier presentation immaterial. These are applications of the existing normalization, representation, pure-compiler and pinned counting/order suppliers, together with the new source-check reflection; no separate count, cutoff or optimizer theorem is installed.")),
            Paragraph(Text("The result is mathematical finite attainment for arbitrary nonnegative real prices. It supplies no effective real comparator or efficiency bound, no physical memory or energy optimum, and no freedom to combine separately attainable state and address minima or exchange the same-source maximum with a sum. Zero address prices and integral B/k are included. Zero state price, negative address prices and additional priced resources are outside this argument. The general prescribed-route/prototype exact-trace compiler remains a separate contract.")))));

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
