using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence;

internal sealed class HardinActualTransfersDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinActualTransfers.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full transfer matrices for the diagonal and square strip graphs.",
        H("Actual strip states and their continuations"),
        Blocks(
            Node("column-transfer", "C", "Unrestricted column transfer", DescribeRole.Definition,
                "For every h≥0, C h acts on all functions from Fin(h+1) to Fin 3. The entry at current column p and successor q is one exactly when p and q differ across each horizontal bond and both diagonals. There are no within-column bonds."),
            Node("proper-word", "Word", "Proper word states", DescribeRole.Definition,
                "For every k≥0, the states are length k+1 words in Fin 3 whose adjacent labels differ. There are 3·2^k such words."),
            Node("word-transfer", "wordTransfer", "Diagonal and square row transfers", DescribeRole.Definition,
                "Both matrices act on Word k. The diagonal matrix R has entry one exactly when the two opposite diagonals differ at each pair of adjacent positions. The square matrix S has entry one exactly when vertically aligned labels differ. Horizontal edges are enforced by the state type."),
            Node("column-power", "column_power", "All column powers", DescribeRole.Theorem,
                "At every h,m≥0 and current column p, (C h)^m applied to the all-one vector equals the existing columnV m p. The zero-step vector has value one at every column. The successor step sums over the exact cross-bonds."),
            Node("column-continuations", "column_continuations", "The number of literal column tails", DescribeRole.Theorem,
                "For every fixed current column and every m≥0, the power vector entry is the number of m-column tails satisfying the immediate cross-bond conditions. The existing column reconstruction supplies the correspondence."),
            Node("column-count", "column_count", "Counting the actual strip by columns", DescribeRole.Theorem,
                "For every h,m≥0, summing the vector for m transitions gives the labelled three-colour count of the diagonal strip with height h+1 and width m+1. At width one the graph has no edges and all 3^(h+1) columns contribute."),
            Node("word-continuations", "word_continuations", "The number of literal row tails", DescribeRole.Theorem,
                "For either bond rule, every k,m≥0 and fixed proper row p, the power vector entry counts all m-row tails with the required horizontal and inter-row bonds. Every legal successor is one proper word and contributes once."),
            Node("word-count", "word_count", "Counting the actual strip by rows", DescribeRole.Theorem,
                "For both bond rules and every k,m≥0, sum the power vector indexed by all proper words. The result counts labelled three-colourings of the strip with width k+1 and height m+1. The source uses the diagonal matrix for widths at least two and the square matrix at widths two and three."),
            Node("class-powers", "powerOnes_of_rows", "Pullback of a quotient power", DescribeRole.Theorem,
                "For finite state sets A and B and matrices T and Q over the integers, fix a map c from A to B. If every row of T has total Q(c(a),b) in the fibre over b, then for every a and every m≥0, the a-entry of T^m on ones equals the c(a)-entry of Q^m on ones. Regroup the successor sum into fibres at each induction step. The degree-zero case includes every state."),
            Node("lag-relation", "IsLagRelation", "Lag convention", DescribeRole.Definition,
                "For a length-d coefficient list c, the relation with shift b equates T^(b+d) on ones with the sum of c_j times T^(b+d−j) on ones for j from one through d. Diagonal strip columns use b=1 and proper row words use b=0."),
            Paragraph(Text("The labelled counts here feed the existing normalization by complementary pairs. For the connected diagonal rectangles, multiplying by 2 raised to the number of cells and adding the established correction gives the literal count after division by 48. The edgeless width-one count follows its separate source formula.")))));

    private static DocumentBlock Node(string id, string name, string title, DescribeRole role, string statement) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(statement))), role);
}
