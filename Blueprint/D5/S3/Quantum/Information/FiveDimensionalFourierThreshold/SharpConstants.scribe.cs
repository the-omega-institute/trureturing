using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.FiveDimensionalFourierThreshold;

internal sealed class SharpConstantsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/SharpConstants.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Squared radical identities and rational comparisons certify the deficit and residual coefficients used for the sharp bound.",
        H("Radicals and exact budget constants"),
        Blocks(
            Describe.Lean(DescribeId.Create("five-sharp-sharpcutoff-eq"),
                DeclarationHandle.Create(Prefix + "sharpCutoff_eq"), H("The proposed sharp cutoff"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact cutoff (14 + 2√5)/5 equals four times the square of the critical singular value c."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("five-sharp-sharp-budget-lt"),
                DeclarationHandle.Create(Prefix + "sharp_budget_lt"), H("Joint deficit budget"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The quantity 2c(1−c) is strictly less than 0.075."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("five-sharp-sharp-leakage-bound"),
                DeclarationHandle.Create(Prefix + "sharp_leakage_bound"), H("Leakage bound"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A joint spectral deficit below 0.075 bounds leakage by 0.173 when the leakage is charged at the gap c−h."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("five-sharp-sharp-even-margin"),
                DeclarationHandle.Create(Prefix + "sharp_even_margin"), H("Even-sector margin"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The weighted even-sector coefficient plus the mismatch allowance 0.02 is strictly less than 4c."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("five-sharp-sharp-two-errors"),
                DeclarationHandle.Create(Prefix + "sharp_two_errors"), H("Joint error estimate"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The two square-root errors are bounded by the square root of the product of their combined weights and budgets."))), DescribeRole.Theorem)),
        []));
}
