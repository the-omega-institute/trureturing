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
            Node("result", "Unique decomposition and exact legal gap shape",
                "Three assertions hold jointly. For every finite window word w there "
                + "exists exactly one p in Cuts with Clean(p) and Join(p)=w. For every "
                + "w, the number of separator-gap pairs in Split(w) is count(U,w)+count(V,w). "
                + "For every w, Legal(w) holds if and only if, for every gap g in "
                + "Gaps(Split(w)), there exists exactly one Gap q with GapWord(q)=g. "
                + "All natural exponents, empty words, empty gaps and words with no "
                + "neutral letters are included.", DescribeRole.Theorem,
                "Each neutral letter removes both possible seam obstructions. Inside "
                + "a gap the forbidden adjacent pairs are YX, YZ, ZX and ZZ. After "
                + "Y or Z, every remaining letter must be Y; before them, every "
                + "letter is X. Hence a legal gap has the displayed shape. Counts of "
                + "X, Z and Y recover its three exponents. Recursive splitting and "
                + "joining are inverse when the gap alphabet condition holds."))));

    private static DocumentBlock Node(string name, string title, string statement,
        DescribeRole role, params string[] proof) => Describe.Lean(
            DescribeId.Create("window-histogram-" + (name == "Gap" ? "gap-data" : name.ToLowerInvariant())),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks([Paragraph(Text(statement)), .. proof.Select(text => Paragraph(Text(text)))]), role);
}
