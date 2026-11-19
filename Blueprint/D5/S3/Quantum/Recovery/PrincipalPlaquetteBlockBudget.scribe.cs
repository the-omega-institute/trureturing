using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class PrincipalPlaquetteBlockBudgetDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coherent rows strengthen the one-party plaquette obstruction for native paired channels.",
        H("Coherent block budget for the one-party plaquette obstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("rt-native-coherent-matrix-unit-row"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Recovery/PrincipalPlaquetteBlockBudget."
                    + "matrixUnit_row_square_le"),
                H("One squared diamond budget per coefficient row"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A tagged rank-one test chooses the column amplitude vector proportional "
                    + "to all the errors in the row. It bounds their squared norm sum by "
                    + "the square of the native unhalved diamond distance."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rt-native-coherent-plaquette-budget"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Recovery/PrincipalPlaquetteBlockBudget."
                    + "paired_improved_one_party_native_diamond"),
                H("Improved one-party phase bound from coherent rows"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For one selected pair of fibres the two row tests give a Frobenius "
                        + "budget. The opposite gauge converts entry errors into signed real "
                        + "budget deficits; a reciprocal-weight Cauchy bound then strengthens "
                        + "the cosine obstruction by a factor of twelve elevenths.")),
                    Paragraph(Text(
                        "Only the first party's phase is used. The native paired-channel "
                        + "identity, labelled fibres and original target coefficients remain "
                        + "hypotheses. No assumption on leakage, common quotient or "
                        + "cross-entry dominance is added."))),
                DescribeRole.Theorem))));
}
