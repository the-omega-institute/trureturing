using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class ShortCommonCoefficientProbeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/ShortCommonCoefficientProbe.";
    private static readonly LibraryNoteRef Kaliski =
        LibraryNoteRef.Create("D5/L/Words/kaliski2017targeted");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every modular coefficient pair has one short first-00 canonical word on all rows.",
        H("Short Common Canonical Fibonacci Probes"),
        Blocks(
            Definition("firstIndex", "The first index above twice the modulus",
                "For a natural H, j=firstIndex(H) is the least index with F(j)>2H. "
                + "The Fibonacci convention is F(0)=0, F(1)=1."),
            Definition("lengthIndex", "The integer-size cutoff",
                "With q=F(firstIndex(H)), m=lengthIndex(H) is the least index with "
                + "F(m)>=H(q+1). The defining set is nonempty."),
            Definition("lengthBound", "The window bound",
                "The window budget is L(H)=(m+2)/3 in natural-number division, "
                + "which is the ceiling of m/3."),
            Definition("windowCoefficients", "The two basis-row coefficients",
                "The coefficient pair of a literal word is its flattened Fibonacci "
                + "evaluation at rows (1,0) and (0,1), in ZMod H."),
            Definition("firstTwoZero", "The first two literal bits",
                "The first two bits of the flattened word are both false."),
            Definition("Covers", "Coefficient saturation by successful nonempty words",
                "Covers(H,L) requires every pair in (ZMod H)^2 to occur as the "
                + "coefficient pair of a nonempty successful literal word of at most "
                + "L windows. Success includes legality at the incoming true seam. "
                + "For a nonempty word it also requires a nonzero last window."),
            Definition("Covers00", "Coefficient saturation with two leading zeros",
                "Covers00(H,L) adds the first-two-zero condition to the same "
                + "nonempty successful word family."),
            Definition("D", "The unrestricted saturation depth",
                "D(H) is the infimum of the positive natural budgets satisfying "
                + "Covers(H,L), in WithTop Nat. An empty set has infimum infinity."),
            Definition("D00", "The first-00 saturation depth",
                "D00(H) is the infimum of the positive budgets satisfying "
                + "Covers00(H,L), with the same infinity convention."),
            Describe.Lean(
                DescribeId.Create("short-common-canonical-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("One bounded canonical word works on every row and after every legal prefix"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Kaliski),
                Blocks(
                    Paragraph(Text(
                        "For every H>=2, j is at least five and 2H<F(j)<4H. For every "
                        + "pair A,B in ZMod H there is one nonempty word w of at most "
                        + "L(H) windows, beginning with two zero bits and having a "
                        + "successful canonical End. Its coefficient pair is (A,B), "
                        + "and for every row u,v its value is Au+Bv. The word may depend "
                        + "on H,A,B; it is common to all rows.")),
                    Paragraph(Text(
                        "For either initialization bit epsilon and every literal prefix p "
                        + "legal at that bit, initialized(epsilon,p++w) returns some "
                        + "strictly positive natural N. This includes the empty legal "
                        + "prefix and the zero modular coefficient pair. Hence the "
                        + "modular zero readout never stands for the integer zero.")),
                    Paragraph(Text(
                        "The saturation depths satisfy D(H)<=D00(H)<=L(H). An explicit "
                        + "logarithmic estimate is L(H)<=2 floor(log_2 H)+5, where the "
                        + "integer logarithm Nat.log takes base two. In terms of the real "
                        + "natural logarithm, L(H)<=7 log(H)/log(2), which gives O(log H).")),
                    Paragraph(Text(
                        "A shifted rational Fibonacci grid supplies H<=n<H(q+1) with "
                        + "the prescribed integer and shifted-Zeckendorf residues. "
                        + "The Zeckendorf support of n lies below m. Place its digits "
                        + "at their original indices in an IndependentWord. The public "
                        + "LiteralWindowEnd equivalence supplies its successful inverse "
                        + "with the required length bound. Its padded-bit and numeric "
                        + "readout identities give the two basis coefficients; linearity "
                        + "extends them to shiftedFibSum(n)u+nv on every modular row. "
                        + "Its positive natural value excludes the empty word, and "
                        + "the two leading zeros preserve legality at either seam. "
                        + "The existing literal End theorem supplies positivity after "
                        + "a legal prefix. Finally, let k=Nat.log 2 H>=1. The chain "
                        + "H(q+1)<=4H^2+H<2^(2k+5)<=4^(k+3)<F(3k+13)<=F(4k+12) "
                        + "bounds m by 4k+12, using the existing powerDigits_bound "
                        + "estimate 4^n<F(3n+4)."))),
                DescribeRole.Theorem),
            Describe.Remark(
                DescribeId.Create("short-common-modular-hofstadter-antecedent"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The modular Hofstadter G antecedent"),
                AssessedProvenance.FromLiterature(Kaliski),
                Blocks(Paragraph(Text(
                    "Kaliski, Appendix B, Lemma 5, Theorem 2 and Corollary 2 give "
                    + "simultaneous modular Hofstadter G pairs and logarithmic "
                    + "Zeckendorf length. The first-index constants used here adapt "
                    + "that arithmetic construction. The literal window alphabet, "
                    + "first two zeros, terminal trimming and arbitrary-prefix "
                    + "canonical End are additional statements.")))))));

    private static DocumentBlock Definition(string selector, string title, string prose) =>
        Describe.Lean(
            DescribeId.Create("short-common-" + selector.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + selector), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
}
