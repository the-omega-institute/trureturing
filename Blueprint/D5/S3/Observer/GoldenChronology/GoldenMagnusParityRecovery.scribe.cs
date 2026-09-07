using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.GoldenChronology;

internal sealed class GoldenMagnusParityRecoveryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For a specified length, center-only recovery of every legal golden factor holds exactly when that length is even.",
        H("Magnus Center and Window Parity"),
        Blocks(
            Describe.Remark(
                DescribeId.Create("golden-magnus-parity-recovery-source"),
                DeclarationHandle.Create("D5/S3/Observer/GoldenChronology/GoldenMagnusParityRecovery.center_recovers_fixed_length_iff_even"),
                H("Source-linked mathematical interpretation"),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For a specified length, center-only recovery of every legal golden factor holds exactly when that length is even.")),
                    Paragraph(Text("Even-length balance and integral parity recover the omitted count. At each odd length the two distinct legal palindromes have zero center. Every same-length central fiber contains at most two word contents.")),
                    Paragraph(Text("This mirror supplies commentary only. The named Lean declaration and its kernel report own the exact statement and verification status.")))))));
}
