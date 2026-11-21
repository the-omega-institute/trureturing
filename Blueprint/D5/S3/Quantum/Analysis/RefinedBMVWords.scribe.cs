using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class RefinedBMVWordsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nonnegative shift of the cubic trace gap",
        H("A nonnegative shift of the cubic trace gap"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("refinedbmvwords-tracegap-shift"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/RefinedBMVWords.traceGap_shift"),
                H("A nonnegative shift of the cubic trace gap"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The cyclic word counts give the trace gap in terms of a commutator. A nonnegative scalar shift adds a nonnegative multiple of a squared norm."))),
                DescribeRole.Theorem))));
}
