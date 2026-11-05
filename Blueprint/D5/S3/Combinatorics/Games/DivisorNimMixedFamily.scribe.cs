using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Games;

internal sealed class DivisorNimMixedFamilyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Games/DivisorNimMixedFamily.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete mixed two/four formula for the actual multiset game.", H("The complete mixed two/four formula"), Blocks(
            Paragraph(Text("The mathematical targets are due to Satyam Tyagi. This module supplies their Lean proofs in the native Divisor Nim model, reusing the existing independently checked game-theoretic library.")),
            Paragraph(Text("Write A for r copies of two and s copies of four, where r,s are positive, and omit a varying heap of size zero. The actual SG sequence is one at n congruent to one modulo four, two at n congruent to three modulo four, and three times the parity of r+floor(n/2) at even n. Multiplicities and n are unbounded.")),
            Node("formula", "The complete native mixed formula", "mixed_formula_statement", "The proof uses the established native recurrence and outcome theorem. Winning even boards have options of values zero, one and two. Odd phases follow by strong induction. A second induction on the number of fours excludes value three from all followers of winning even boards. Deleting the last two is included: the remaining pure-four board has a legal four-to-two option with value three by the smaller-family theorem, or the explicitly proved one-two boundary. The omitted-zero singleton-four case is handled directly. No finite table substitutes for the infinite-family proof.")), []));
    private static DocumentBlock Node(string id, string title, string declaration, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
