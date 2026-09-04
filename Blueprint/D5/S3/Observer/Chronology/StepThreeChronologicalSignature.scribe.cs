using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Chronology;

internal sealed class StepThreeChronologicalSignatureDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/Chronology/StepThreeChronologicalSignature.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Factorially normalized degree-three Chen signatures truncate multiplicatively to step two and realize chronological reversal by an explicit antipode.",
        H("Step-Three Chronological Signature"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("step-three-chronological-reverse-neg"),
                DeclarationHandle.Create(
                    Prefix + "chronological_step_three_reverse_neg"),
                H("Reverse-and-negate is the degree-three antipode"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The denominator-free coordinates store degree one, twice degree two, and six times degree three. Their Chen composition is associative and extends the frozen step-two signature.")),
                    Paragraph(Text(
                        "For ring-valued observations, the explicit degree-three antipode is a left and right Chen inverse and reverses multiplication order.")),
                    Paragraph(Text(
                        "Reversing the event word and negating every event therefore maps its complete degree-three chronological signature to that antipode."))),
                DescribeRole.Theorem))));
}
