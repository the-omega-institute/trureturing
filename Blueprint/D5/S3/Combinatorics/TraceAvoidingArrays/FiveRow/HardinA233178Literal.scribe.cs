using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays.FiveRow;

internal sealed class HardinA233178LiteralDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Literal.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact five-row six-colour source count and a division-free chromatic correspondence.",
        H("Literal arrays and scanner fibres"), Blocks(
            Paragraph(Text("The domain is Fin 5 times Fin n. Every cell has one of six colours, "
                + "the top left cell is zero, and first appearances are ordered by the strict rank i*n+j. "
                + "Colours may be absent. Every horizontal, diagonal and antidiagonal pair across "
                + "consecutive columns has distinct colours whose sum is not five. Vertical and "
                + "wraparound pairs have no restriction. All recurrence arithmetic is in the integers.")),
            Node("swap", "Exchange of the two noninitial labels", "The involution exchanges one "
                + "and two and fixes zero.", DescribeRole.Definition),
            Node("absent", "A whole-word absence indicator", "The integer indicator is one "
                + "exactly when the specified label never occurs, including for the empty word.",
                DescribeRole.Definition),
            Node("normalization_result", "Exact scanner symmetrization", "For every natural k and every "
                + "word q from Fin k into Fin 3, write W(q)=rowWeight((false,false),q) "
                + "and A(q,c)=absent(q,c). Then "
                + "4*(W(q)+W(swap composed with q))="
                + "2^k*(1+A(q,1)+A(q,2)+5*A(q,1)*A(q,2)). "
                + "The product term retains the all-zero case. The induction first establishes "
                + "2*rowWeight((true,false),q)=2^k*(1+A(q,2)), then splits on the first label. "
                + "No colour-occurrence or surjectivity assumption is imposed. This pointwise "
                + "identity does not by itself identify a graph count or settle A233178.", DescribeRole.Theorem),
            Node("Array", "The literal function domain", "Arrays are arbitrary functions on the five "
                + "rows and n columns into a finite colour set.", DescribeRole.Definition),
            Node("rank", "Strict row-major rank", "The rank of cell (i,j) is i*n+j.", DescribeRole.Definition),
            Node("Edges", "Exactly the constrained pairs", "An edge goes one column to the right "
                + "and changes the row by at most one. There is no modular indexing.", DescribeRole.Definition),
            Node("Normal", "Literal first appearances", "Every occurrence of two, three or four has "
                + "an earlier one, and every occurrence of three has an earlier two. Earlier means "
                + "strictly smaller literal row-major rank.", DescribeRole.Definition),
            Node("Legal", "The full source predicate", "The predicate conjoins the pinned initial "
                + "cell, every edge restriction and the first-appearance conditions. It imposes no "
                + "surjectivity or orbit divisor.", DescribeRole.Definition),
            Node("a", "Literal cardinality", "The count is the cardinality of the legal function "
                + "subtype, expressed as a finite filtered set. Only positive widths enter FullE.", DescribeRole.Definition),
            Node("FullE", "The unchanged event", "For every natural n greater than eleven, the "
                + "literal count satisfies the ten-term integer recurrence, with coefficients in lag "
                + "order 192, 31744, -3178496, -170917888, 13992198144, 99857989632, "
                + "-17660905521152, 211106232532992, 2533274790395904, -40532396646334464. "
                + "There is no upper cutoff, additional onset, generating-function assertion or "
                + "minimal-order assertion.", DescribeRole.Definition),
            Node("word", "Exact row-major reindexing", "The product-to-Fin equivalence enumerates "
                + "the cells at their actual rank. It is a bijection and preserves the strict earlier "
                + "relation used in Normal.", DescribeRole.Definition),
            Node("Proper", "Proper pair-label arrays", "Complementary pairs become the three labels. "
                + "Properness requires different labels at exactly the literal edges.", DescribeRole.Definition),
            Node("Anchored", "Anchored proper pair labels", "The initial pair label is zero and the "
                + "array is proper. There is no occurrence requirement on the other labels.", DescribeRole.Definition),
            Node("scanner_count", "Exact scanner pushforward", "Twice the literal source count is "
                + "the sum of the existing scanner weights over the anchored proper three-label "
                + "arrays. The factor two comes from exchanging colours zero and five, which leaves "
                + "the pair labels, scanner permission and scanner state unchanged. The existing "
                + "scanner_fibres theorem counts the exact individual-colour fibres after the "
                + "row-major bijection. The scanner starts in (false,false) and reads word(q) "
                + "in that same row-major order. This statement includes every width.", DescribeRole.Theorem),
            Node("pairCount", "Anchored chromatic count", "This integer finite sum counts every "
                + "proper three-label array with its initial label zero, including arrays missing "
                + "one label.", DescribeRole.Definition),
            Node("source_count", "Exact missing-label correction", "For n at least two, sixteen "
                + "times a(n) equals 32^n times (pairCount(n)+2). Exchanging labels one and two "
                + "preserves anchored properness. Summing the existing pointwise normalization "
                + "identity therefore counts both scanner orders. Each missing-label fibre has "
                + "exactly one member: the alternating column-parity colouring. Its uniqueness "
                + "is a specialization of HardinA233260Literal.two_label_classification: "
                + "the literal graph contains every horizontal and antidiagonal edge required "
                + "there, the anchor fixes the first label to zero, and the omitted label fixes "
                + "the other label. This uniqueness specialization and the scanner pushforward "
                + "use the existing classification and scanner-fibre identities. The pointwise "
                + "normalization_result is proved above by induction on the word length. "
                + "An anchored proper array cannot miss "
                + "both nonzero labels. These facts supply the correction two without a source "
                + "surjectivity condition or an imposed orbit divisor.", DescribeRole.Theorem),
            Node("chromaticCount", "Unrestricted chromatic cardinality", "This counts all proper "
                + "three-label arrays on the literal graph, with every initial label allowed.", DescribeRole.Definition),
            Node("chromatic_source_count", "Division-free literal source bridge", "For every "
                + "n at least two, 48*a(n) equals 32^n*(chromaticCount(n)+6). Permuting zero "
                + "with a specified initial label gives a bijection between the three anchored "
                + "fibres. The proof multiplies the anchored identity by three; it uses no "
                + "truncated subtraction or division.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace("_", "-").Replace(".", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
