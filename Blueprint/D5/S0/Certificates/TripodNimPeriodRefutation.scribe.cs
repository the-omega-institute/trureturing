using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class TripodNimPeriodRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/TripodNimPeriodRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/hennessey2024tree");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A periodic orbit of D(3,10) has least period 264, which does not divide 3280.",
        H("Tripod Nim: the printed period assertion"),
        Blocks(
            Describe.Lean(DescribeId.Create("tripod-transition"),
                DeclarationHandle.Create(Prefix + "transition"),
                H("The transition of the three-row system"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Section 9.3 uses three Boolean rows with 2n+3 columns. Columns are "
                    + "numbered from the left, and rows are listed from bottom to top. "
                    + "A step shifts left, appends zeros, and inserts one into each row "
                    + "whose departing bit was zero. Each insertion uses the leftmost zero "
                    + "outside the first n columns and outside the columns already chosen "
                    + "by this step. An unavailable insertion gives an absorbing undefined "
                    + "state, so a returning present board has only defined steps."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("tripod-printed-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("Conjecture 2 as printed"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Conjecture 2 on printed page 30 of arXiv:2401.07943v1 says that "
                    + "every periodic orbit of D(3,n) has a period dividing 2(4n)(4n+1). "
                    + "The definition quantifies over all three-row periodic boards of "
                    + "the transition and uses Mathlib's minimalPeriod. Requiring the "
                    + "least period to divide the displayed number is equivalent to the "
                    + "existence of such a period. Remark 9.2 reports confirmation for "
                    + "n at most nine."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("tripod-period-refutation"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A period of 264 at n=10"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "With bit zero representing the leftmost column, the rows of the "
                    + "chosen board encode 1, 2047 and 2042 from bottom to top. The "
                    + "word evaluator returns to this board after 264 steps, and fails "
                    + "to return after 24, 88 and 132 steps. Decoding commutes with "
                    + "each transition and is injective, which transfers both return "
                    + "and nonreturn statements to the Boolean board semantics.")),
                    Paragraph(Text(
                    "Every proper divisor of 264 divides 132, 88 or 24, so the least "
                    + "period is exactly 264. At n=10 the printed expression is 3280, "
                    + "and 3280 equals 12 times 264 plus 112. This contradicts exactly "
                    + "the printed Conjecture 2. No initial-state reachability assertion "
                    + "is needed. No priority for the example, no conclusion about "
                    + "other results in the paper, and no corrected formula are claimed."))),
                DescribeRole.Theorem))));
}
