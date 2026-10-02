using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class WindowHistogramLegalCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Neutral input positions give a unique legal gap code and exact five-window histogram counts.",
        H("Neutral Gaps and Exact Histogram Counts of Legal Fibonacci Window Words"),
        Blocks(
            Paragraph(Text("Use the literal windows X=100, Y=001, Z=101, U=000 and V=010, "
                + "with bits written low to high. A word is a finite list of these windows. "
                + "Legal(w) means legal(false,flatten(w)): the incoming seam is zero and "
                + "there are no adjacent occupied bits. The first window has no extra "
                + "restriction. U and V each occupy one input position, including when "
                + "neighboring gaps are empty. End acceptance is a separate condition. "
                + "The existing triple(false,d,false) constructs U for false and V for true.")),
            Node("Free", "Gaps without neutral letters",
                "Free(g) means that every window in g differs from U and V. "
                + "Thus g uses only X, Y and Z; the empty gap is allowed.",
                DescribeRole.Definition),
            Node("Gap", "Gap exponents",
                "A Gap is a triple (x,z,y), where x and y are arbitrary natural numbers "
                + "and z is Boolean. The Boolean central exponent is zero or one.",
                DescribeRole.Definition),
            Node("gap", "The canonical gap word",
                "GapWord(x,z,y)=X^x Z^[z] Y^y, where [false]=0 and [true]=1. "
                + "The powers denote literal repeated input windows.",
                DescribeRole.Definition),
            Node("Cuts", "An ordered decomposition",
                "Cuts consists of a first gap g0 and a finite ordered list of pairs "
                + "(di,gi), with di Boolean and gi a gap word.", DescribeRole.Definition),
            Node("join", "Reconstructing a word",
                "Join(g0,[(d1,g1),...,(dt,gt)]) is "
                + "g0 triple(false,d1,false) g1 ... triple(false,dt,false) gt.", DescribeRole.Definition),
            Node("gaps", "All gaps, including empty gaps",
                "Gaps(p) is the ordered list [g0,g1,...,gt]. It always contains "
                + "the first gap, even when the input word is empty.", DescribeRole.Definition),
            Node("Clean", "The gap alphabet condition",
                "Clean(p) means Free(g) for every g in Gaps(p). "
                + "Neutral letters occur only at the designated separators.", DescribeRole.Definition),
            Node("split", "Splitting at actual neutral positions",
                "Split(w) retains the first gap and every neutral letter together with "
                + "the following gap. Leading, trailing and consecutive neutral letters "
                + "retain their corresponding empty gaps.", DescribeRole.Definition),
            Node("Code", "Canonical legal-word codes",
                "A Code consists of a Gap and an ordered list of Boolean/Gap pairs. "
                + "Every Boolean specifies one actual U or V input position.", DescribeRole.Definition),
            Node("codeCuts", "Expanding gap exponents",
                "CodeCuts replaces each Gap in a Code by its canonical gap word.",
                DescribeRole.Definition),
            Node("codeWord", "Reconstructing the literal word",
                "CodeWord(p)=Join(CodeCuts(p)).", DescribeRole.Definition),
            Node("readGap", "Reading gap exponents",
                "ReadGap reads the X count, whether the Z count is one, and the Y count.",
                DescribeRole.Definition),
            Node("readCode", "Reading a canonical code",
                "ReadCode reads every gap and retains all ordered neutral letters.",
                DescribeRole.Definition),
            Node("terminalGap", "The final gap",
                "TerminalGap(p) selects the final gap, including an empty final gap.",
                DescribeRole.Definition),
            Node("inventory", "Counts recovered from gap exponents",
                "Inventory(p) assigns the sums of the X and Y gap exponents, the number "
                + "of gaps carrying Z, and the counts of false/true neutral Booleans.",
                DescribeRole.Definition),
            Node("HistogramWords", "An exact literal-word histogram fiber",
                "For any function h from Window to natural numbers, HistogramWords(h) "
                + "contains exactly the legal literal words with count(f,w)=h(f) for every f.",
                DescribeRole.Definition),
            Node("HistogramCodes", "The corresponding canonical-code fiber",
                "HistogramCodes(h) contains the Codes whose Inventory is h.",
                DescribeRole.Definition),
            Node("EndpointWords", "Exact last-window fibers",
                "EndpointWords(h,f) retains precisely the literal words in HistogramWords(h) "
                + "whose last window is f. The empty word belongs to none of these fibers.",
                DescribeRole.Definition),
            Node("PositiveEndpointWords", "Positive F labels in a terminal fiber",
                "PositiveEndpointWords(h,f) further requires End acceptance from zero initial "
                + "seam and flag, using the existing run and endable definitions.",
                DescribeRole.Definition),
            Node("rawCode", "Indexed neutral and gap assignments",
                "For t indexed neutral Booleans and t+1 indexed Gaps, RawCode retains "
                + "gap 0 and then each neutral Boolean together with its successor gap.",
                DescribeRole.Definition),
            Node("histogram", "Five prescribed multiplicities",
                "Histogram(a,b,c,r,s) assigns a to X, b to Y, c to Z, r to U and s to V.",
                DescribeRole.Definition),
            Node("Factors", "Independent subset and weak-composition factors",
                "With t=r+s, Factors(a,b,c,r,s) consists of an r-element subset of Fin(t), "
                + "a c-element subset of Fin(t+1), and the existing ArrowWilfGapData.Gaps "
                + "weak compositions of a and b into t+1 ordered slots.", DescribeRole.Definition),
            Node("factorRaw", "Reconstructing indexed assignments",
                "The first subset specifies U positions, its complement V positions; "
                + "the second subset specifies Z-bearing gaps, and the two weak compositions "
                + "specify the X and Y exponents of every gap.", DescribeRole.Definition),
            Node("result", "Unique decomposition, histogram counts and terminal labels",
                "The assertions hold jointly. For every finite window word w there "
                + "exists exactly one p in Cuts with Clean(p) and Join(p)=w. For every "
                + "w, the number of separator-gap pairs in Split(w) is count(U,w)+count(V,w). "
                + "For every w, Legal(w) holds if and only if, for every gap g in "
                + "Gaps(Split(w)), there exists exactly one Gap q with GapWord(q)=g. "
                + "For every w, Legal(w) holds if and only if there is exactly one Code p "
                + "with CodeWord(p)=w. For every Code p, its word ends in X precisely "
                + "when its final gap has x>0, z=false and y=0; it ends in Z precisely "
                + "when its final gap has z=true and y=0. "
                + "For every p and f, count(f,CodeWord(p))=Inventory(p)(f). For every "
                + "histogram h there is a bijection from HistogramCodes(h) to "
                + "HistogramWords(h) sending p to CodeWord(p). "
                + "For all natural a,b,c,r,s and t=r+s, there is also a bijection "
                + "from Factors(a,b,c,r,s) to HistogramWords(Histogram(a,b,c,r,s)), "
                + "whose word is CodeWord(RawCode(FactorRaw(p))). This word fiber is finite "
                + "and its exact cardinality is binom(t,r) binom(t+1,c) "
                + "multichoose(t+1,a) multichoose(t+1,b). The standard multichoose "
                + "counts ordered weak compositions; for these positive slot counts it "
                + "equals binom(a+t,t) and binom(b+t,t), respectively. "
                + "Write H for this histogram cardinality and N_f for its exact "
                + "terminal-fiber cardinality. N_U is zero if r=0 and otherwise "
                + "H(a,b,c,r-1,s); N_V is zero if s=0 and otherwise H(a,b,c,r,s-1); "
                + "N_Y is zero if b=0 and otherwise H(a,b-1,c,r,s). N_X is zero if "
                + "a=0 and otherwise binom(t,r) binom(t,c) multichoose(t+1,a-1) "
                + "multichoose(t,b). N_Z is zero if c=0 and otherwise binom(t,r) "
                + "binom(t,c-1) multichoose(t+1,a) multichoose(t,b). These guards "
                + "implement the convention that a negative histogram parameter gives "
                + "zero. The zero-slot multichoose is one at multiplicity zero and "
                + "zero at every positive multiplicity. Thus at t=0, N_U=N_V=0, "
                + "N_X is the indicator of a>0 and b=c=0, N_Y is the indicator of "
                + "b>0 and c in {0,1}, and N_Z is the indicator of c=1 and b=0. "
                + "For nonzero total multiplicity, the five terminal-fiber cardinalities "
                + "sum to the histogram cardinality. The zero histogram has cardinality "
                + "one and its only word is empty. Every fiber ending in a letter with "
                + "zero multiplicity is empty, and every histogram with c>t+1 is empty. "
                + "For every h and f, the positive F fiber has cardinality zero when f=U, "
                + "and otherwise has the full terminal-fiber cardinality. "
                + "All natural exponents, empty words, empty gaps and words with no "
                + "neutral letters are included.", DescribeRole.Theorem,
                "Each neutral letter removes both possible seam obstructions. Inside "
                + "a gap the forbidden adjacent pairs are YX, YZ, ZX and ZZ. After "
                + "Y or Z, every remaining letter must be Y; before them, every "
                + "letter is X. Hence a legal gap has the displayed shape. Counts of "
                + "X, Z and Y recover its three exponents. Recursive splitting and "
                + "joining are inverse when the gap alphabet condition holds. Reading the "
                + "exponents and rebuilding are inverse on all legal words. Since neutral "
                + "letters differ from X and Z, these endpoints require a nonempty final "
                + "gap of the stated form.",
                "Index the neutral positions by Fin(t) and the gaps by Fin(t+1). "
                + "Their U positions and Z-bearing gaps are independent subsets of the "
                + "prescribed sizes. The X and Y exponents independently form the existing "
                + "ordered weak-composition data. Reading and reconstruction give both "
                + "directions of the literal-word bijection. Apply the pinned subset and "
                + "weak-composition cardinalities directly. The endpoint sum uses the "
                + "standard partition by the last window, and the F labels use the public "
                + "execution theorem and the standard last-item decomposition. "
                + "Appending U, V or Y preserves legality because its first bit is "
                + "zero. Removing that last window and appending it again are inverse, "
                + "including for an empty prefix, and give the three guarded H formulas. "
                + "For a terminal X, the last Z slot is absent, the last Y part is "
                + "zero, and the last X part is positive. For a terminal Z, the last "
                + "Z slot is present and the last Y part is zero. The reversible "
                + "factor encoding restricts to each of these exact fibers. Erasing "
                + "the last available slot gives the Y weak composition over t slots. "
                + "Subtract one from the positive last X part by the existing "
                + "positive-gap equivalence; count the Z subsets by the standard "
                + "powerset-cardinality formulas. These operations retain all "
                + "remaining independent factors and yield the X and Z formulas.",
                "The standard counting inputs are described by MIT Mathematics for "
                + "Computer Science, Corollary 15.5.3 and Rule 15.6.3. Flajolet and "
                + "Sedgewick, Analytic Combinatorics, discuss Smirnov words (pp. 204-205), "
                + "Carlitz compositions (pp. 262-263), and locally constrained words "
                + "(pp. 349-350). The inspected sections supply general methods; they "
                + "do not state this same five-window histogram and terminal-fiber result. "
                + "This is a bounded literature finding, not a claim of universal novelty."))));

    private static DocumentBlock Node(string name, string title, string statement,
        DescribeRole role, params string[] proof) => Describe.Lean(
            DescribeId.Create("window-histogram-" + (name == "Gap" ? "gap-data" : name.ToLowerInvariant())),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks([Paragraph(Text(statement)), .. proof.Select(text => Paragraph(Text(text)))]), role);
}
