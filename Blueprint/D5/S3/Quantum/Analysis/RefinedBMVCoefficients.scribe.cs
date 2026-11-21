using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class RefinedBMVCoefficientsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A rational identity for the cubic trace defect",
        H("A rational identity for the cubic trace defect"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("refinedbmvcoefficients-cubicdefect-eq-cyclic"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/RefinedBMVCoefficients.cubicDefect_eq_cyclic"),
                H("A rational identity for the cubic trace defect"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The symmetric denominator makes the rational correction cancel in the cyclic sum. This identity is used to group all three-step walks at each center."))),
                DescribeRole.Theorem))));
}
