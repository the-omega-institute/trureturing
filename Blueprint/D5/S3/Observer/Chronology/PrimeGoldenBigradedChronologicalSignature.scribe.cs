using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Chronology;

internal sealed class PrimeGoldenBigradedChronologicalSignatureDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/Chronology/PrimeGoldenBigradedChronologicalSignature.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime-factor count and Zeckendorf-selected short-step count form an additive bigrading beside the chronological Hopf signature.",
        H("Prime-Golden Bigraded Chronological Signature"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-golden-bigraded-time-reversal"),
                DeclarationHandle.Create(
                    Prefix + "prime_golden_bigraded_time_reversal_laws"),
                H("Bigrading survives reversal while Magnus orientation flips"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Chronological concatenation multiplies the step-two signature and adds two unsigned degrees: prime-event count with multiplicity and the count of Zeckendorf-selected short golden steps.")),
                    Paragraph(Text(
                        "Reverse-and-negate applies the Hopf antipode to the chronological component while preserving the bidegree. The first parity character is the Liouville value of the prime product. The second is the product of local golden long-short signs.")),
                    Paragraph(Text(
                        "For a word contained in one prime channel, the scalar frequency and terminal Euler phase factor through the bidegree. The Magnus coordinate retains oriented order and changes sign under reversal."))),
                DescribeRole.Theorem))));
}
