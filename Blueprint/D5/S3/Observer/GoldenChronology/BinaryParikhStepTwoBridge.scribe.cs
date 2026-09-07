using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.GoldenChronology;

internal sealed class BinaryParikhStepTwoBridgeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The ordered integer matrix product realizes both letter counts and the scattered true-before-false count.",
        H("Binary Parikh and Chen Observer"),
        Blocks(
            Describe.Remark(
                DescribeId.Create("binary-parikh-step-two-bridge-source"),
                DeclarationHandle.Create("D5/S3/Observer/GoldenChronology/BinaryParikhStepTwoBridge.binary_doubled_magnus_center"),
                H("Source-linked mathematical interpretation"),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The ordered integer matrix product realizes both letter counts and the scattered true-before-false count.")),
                    Paragraph(Text("Its central doubled Magnus coordinate is twice the ordered-pair count minus the product of the two letter counts. Unrestricted binary words retain an explicit collision.")),
                    Paragraph(Text("This mirror supplies commentary only. The named Lean declaration and its kernel report own the exact statement and verification status.")))))));
}
