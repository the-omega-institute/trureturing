using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class WindowHistogramLegalCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Neutral input positions give a unique gap decomposition of the actual five-window language.",
        H("Neutral Gaps in Legal Fibonacci Window Words"),
        Blocks(
            Paragraph(Text("Use the literal windows X=100, Y=001, Z=101, U=000 and V=010, "
                + "with bits written low to high. A word is a finite list of these windows. "
                + "Legal(w) means legal(false,flatten(w)): the incoming seam is zero and "
                + "there are no adjacent occupied bits. The first window has no extra "
                + "restriction. U and V each occupy one input position, including when "
                + "neighboring gaps are empty. End acceptance is a separate condition.")),
            Node("neutral", "The two neutral letters",
                "Neutral(false)=U and neutral(true)=V. Both have zero low and high bits.",
                DescribeRole.Definition),
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
                + "g0 neutral(d1) g1 ... neutral(dt) gt.", DescribeRole.Definition),
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
            Node("result", "Unique decomposition and exact legal gap shape",
                "Eight assertions hold jointly. For every finite window word w there "
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
                + "gap of the stated form."))));

    private static DocumentBlock Node(string name, string title, string statement,
        DescribeRole role, params string[] proof) => Describe.Lean(
            DescribeId.Create("window-histogram-" + (name == "Gap" ? "gap-data" : name.ToLowerInvariant())),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks([Paragraph(Text(statement)), .. proof.Select(text => Paragraph(Text(text)))]), role);
}
