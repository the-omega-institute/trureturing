using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition;

internal sealed class OriginalCommonTailCompressionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalCommonTailCompression.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original common-tail selectors and informative endpoints",
        H("Original common-tail selectors and informative endpoints"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("originalcommontailcompression-count"),
                DeclarationHandle.Create(Owner + "count"),
                H("Informative endpoints in a paid interval"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The count retains endpoints whose issued index is divisible by the selected cadence. Every complete word remains paid, including endpoints omitted from the compressed transcript."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("originalcommontailcompression-compress"),
                DeclarationHandle.Create(Owner + "compress"),
                H("Compression from an arbitrary original archive"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary k at least two, block width, selector, remembered INITIAL reading, phase family and starting archive, correct execution on a common current scalar and tail produces a binary protocol with one query per potentially informative endpoint. The retained INITIAL target may repeat. The cadence hypothesis states that every literal word has zero increment at omitted endpoints. At each successful response child the scalar and tail are again common. A uniformly rejecting word gives one absorbing future archive and can only serve a homogeneous target. Stops at any endpoint, zero waits, padding and repairs remain in the original execution and its paid horizon."))),
                DescribeRole.Theorem),
            Paragraph(Text("Cadence one keeps every successful binary endpoint and requires no silence premise. Larger cadences retain the repeated-guardrail application, with its original public statement and paid fee. The remembered INITIAL reading is independent of the current scalar; an acquired prefix need not be empty or share its current scalar with that reading.")))));
}
