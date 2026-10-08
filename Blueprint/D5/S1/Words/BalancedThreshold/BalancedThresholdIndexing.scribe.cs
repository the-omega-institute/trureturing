using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.BalancedThreshold;

internal sealed class BalancedThresholdIndexingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A unimodular bracket of an irrational ratio has computed continued-fraction indices.",
        H("Euclidean indexing"),
        Blocks(Describe.Lean(
            DescribeId.Create("balanced-threshold-unimodular-bracket-continuants"),
            DeclarationHandle.Create(
                "D5/S1/Words/BalancedThreshold/"
                + "BalancedThresholdIndexing.unimodular_bracket_continuants"),
            H("Strong coordinate-sum induction classifies the bracketing vectors"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "For an irrational ratio in (0,1), every nonnegative integral pair with "
                + "determinant magnitude one and opposite discrepancy signs consists of "
                + "a computed convergent and a semiconvergent based on its predecessor. "
                + "The multiplier is strictly less than the next digit. Zero coordinates "
                + "and the initial predecessor are included. Unimodularity excludes "
                + "crossing the first complete-quotient ray. Digit subtraction then "
                + "decreases the coordinate sum, and the computed continuant recurrence "
                + "lifts the descended pair. Endpoint multipliers advance the index. "
                + "The theorem identifies vectors; it does not establish coloured return "
                + "bounds or the target critical exponent."))),
            DescribeRole.Theorem))));
}
