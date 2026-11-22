using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class RefinedBMVTracePowerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A dyadic trace-power comparison",
        H("A dyadic trace-power comparison"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("refinedbmvtracepower-trace-mul-two-pow-le"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/RefinedBMVTracePower.trace_mul_two_pow_le"),
                H("A dyadic trace-power comparison"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Schur triangularization and scalar Jensen give the comparison between successive dyadic approximants, which is retained at the Lie–Trotter limit."))),
                DescribeRole.Theorem))));
}
