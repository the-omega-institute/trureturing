using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.BalancedThreshold;

internal sealed class BalancedThresholdSlopeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Certify the quadratic parameter for the odd balanced-threshold family.",
        H("The uniform quadratic slope"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("balanced-threshold-quadratic-tail"),
                DeclarationHandle.Create(
                    "D5/S1/Words/BalancedThreshold/BalancedThresholdSlope.quadraticTail"),
                H("Positive quadratic tail"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The radical formula selects the positive root of "
                    + "(t-2)x squared plus (t-2)(t+1)x minus (t+1)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("balanced-threshold-uniform-slope"),
                DeclarationHandle.Create(
                    "D5/S1/Words/BalancedThreshold/BalancedThresholdSlope.uniformSlope"),
                H("Minority frequency"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The mechanical frequency is 1/(t+3+1/(t+x)). It differs from "
                    + "the minority-to-majority frequency ratio."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("balanced-threshold-quadratic-parameters"),
                DeclarationHandle.Create(
                    "D5/S1/Words/BalancedThreshold/"
                    + "BalancedThresholdSlope.uniform_quadratic_parameters"),
                H("Irrationality and strict uniform bounds"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every integer t at least five, the discriminant lies strictly "
                    + "between consecutive integer squares. Excluding every integer square "
                    + "root establishes irrationality. The quadratic identity gives the "
                    + "reciprocal tail bounds and both strict separation inequalities. "
                    + "The frequency is irrational and lies strictly between 1/(t+4) "
                    + "and 1/(t+3). This theorem alone does not identify the continued "
                    + "fraction or determine a critical exponent."))),
                DescribeRole.Theorem))));
}
