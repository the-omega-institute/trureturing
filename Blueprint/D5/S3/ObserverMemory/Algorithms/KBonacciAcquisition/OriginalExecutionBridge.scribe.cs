using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition;

internal sealed class OriginalExecutionBridgeDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalExecutionBridge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original scanner and selector execution preserve the joint record and fee.",
        H("Original execution on the joint native record"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("original-kbonacci-nativeexecute"),
                DeclarationHandle.Create(Owner + "NativeExecute"),
                H("The original selector on native records"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The recursion uses the same selector, free reading, chronological archive, and finite fuel as original execution. A selected word appends its actual native endpoint and adds exactly one to a successful returned fee."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("original-kbonacci-record-append"),
                DeclarationHandle.Create(Owner + "record_append"),
                H("Appending words to the original record"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For k at least two, the record of an appended literal word is its native run from the original prefix record. The initial prefix and its actual tail are retained, including absorbing rejection."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-kbonacci-output-record"),
                DeclarationHandle.Create(Owner + "output_record"),
                H("The original scalar endpoint"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original output is exactly the endpoint reading of the same original joint record for every positive k and literal word."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-kbonacci-execute-same"),
                DeclarationHandle.Create(Owner + "execute_same"),
                H("Original and native selector execution agree"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For k at least two, arbitrary selector, horizon, original literal prefix, free reading, and chronological archive, original execution equals native execution from that prefix record. The returned label and fee both agree."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-kbonacci-record-history"),
                DeclarationHandle.Create(Owner + "record_history"),
                H("The joint record of a complete original history"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Flattening the same chronological AllowedBlock history gives exactly its native history record. This includes absorbing rejection and either original alphabet."))),
                DescribeRole.Theorem))));
}
