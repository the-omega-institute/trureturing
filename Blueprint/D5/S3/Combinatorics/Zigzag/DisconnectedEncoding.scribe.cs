using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Zigzag;
internal sealed class DisconnectedEncodingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Zigzag/DisconnectedEncoding.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Initial bits and absolute successor words encode labelled zero-charge native paths in both parities.",
        H("Absolute Successor Words"), Blocks(
            Paragraph(Text("False and true specify the two positive starting states. Each successor bit selects one of the four three-step blocks. Start charge, successive bit differences and final negative bit charge telescope to zero. The even cap and the odd final two steps with singleton are separate native constructions.")),
            Describe.Lean(DescribeId.Create("even-code-injection"), DeclarationHandle.Create(Prefix + "evenCodedChoice_injective"),
                H("Even labelled code recovery"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every r at least one, equality of the native balanced coded choices implies equality of both the initial bit and the entire successor word. The starting label determines the bit, and native path recovery determines each word entry. No choice symmetry quotient is taken."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("odd-code-injection"), DeclarationHandle.Create(Prefix + "oddCodedChoice_injective"),
                H("Odd labelled code recovery"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The odd native decoder has the same code injection, at its own tail length and with its singleton cap retained."))), DescribeRole.Theorem)), []));
}
