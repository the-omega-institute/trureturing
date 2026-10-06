using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Infinite;

internal sealed class FixedTailClosedBudgetDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed-tail closed budget.",
        H("Fixed-tail closed budget"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fixedtailclosedbudget-fixed-tail-closed-budget"),
                DeclarationHandle.Create("D5/S1/Digit/Infinite/FixedTailClosedBudget.fixed_tail_closed_budget"),
                H("Finite affine endpoint certificate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Consider finitely many affine observations. Each observation reads one of two "
                        + "terminal scalar coordinates, and both coordinates range over fixed closed intervals. "
                        + "The target for each observation is another closed interval.")),
                    Paragraph(Text(
                        "For a scalar x and target interval [l,u], the excess is max(l-x, max(0,x-u)). "
                        + "The excess of an affine observation over a terminal interval is bounded by the "
                        + "larger excess at the two terminal endpoints.")),
                    Paragraph(Text(
                        "The maximum of the finitely many endpoint excesses is nonnegative. A nonnegative "
                        + "budget admits a fixed pair of terminal values for every value in the two terminal "
                        + "hulls exactly when it is at least this maximum. At the threshold, every pair of "
                        + "terminal values in the hulls satisfies all observations simultaneously.")))
                , DescribeRole.Theorem))));
}
