using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Games;

internal sealed class DivisorNimRevisedTargetsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Games/DivisorNimRevisedTargets.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The refined ceiling at every depth for the actual multiset game.", H("The refined ceiling at every depth"), Blocks(
            Paragraph(Text("The mathematical targets are due to Satyam Tyagi. This module supplies their Lean proofs in the native Divisor Nim model, reusing the existing independently checked game-theoretic library.")),
            Paragraph(Text("For a positive Divisor Nim position P with minimum two-adic depth k and a distinguished heap H in P, the native Sprague--Grundy value is at most 2H - H/2^k + 1, which is at most 2H. No restriction on heap count, size or numerical minimality is used. The original minimum-heap proposition follows immediately.")),
            Node("reference", "Every distinguished heap", "revised_bound_reference", "Induct on minimum depth. Low-depth options fit the previous ceiling. For quotient H/2^k at least three, save the exceptional removal H-2^k: on H it leaves a minimum dyadic heap and fits the old budget; on another heap it cannot be legal. Quotient one uses the prior independent twice-minimum bound; quotient two uses the penultimate independent reference recurrence, with its established large-exponent inequality and exact small-exponent arithmetic."),
            Node("statement", "The requested minimum-heap statement", "revised_bound_statement", "The complete RevisedBoundStatement holds for every positive position, all natural H,k with HasDepth P k, H in P, and H numerically minimum. The theorem includes power-of-two minima; the independent old bound is reused without circularity."),
            Node("chain", "The full chain of inequalities", "revised_bound_chain", "The actual value is bounded by revisedCeiling H k and that ceiling is at most twice H. Divisibility by 2^k and positivity make the dyadic quotient at least one.")), []));
    private static DocumentBlock Node(string id, string title, string declaration, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
