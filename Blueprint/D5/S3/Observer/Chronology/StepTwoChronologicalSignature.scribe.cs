using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Chronology;

internal sealed class StepTwoChronologicalSignatureDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/Chronology/StepTwoChronologicalSignature.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Chronological words form a step-two signature monoid whose doubled logarithmic coordinate obeys the degree-two BCH law.",
        H("Step-Two Chronological Signature"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("step-two-signature"),
                DeclarationHandle.Create(Prefix + "StepTwoSignature"),
                H("Step-two signature"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A step-two signature stores degree one together with twice degree two, "
                        + "so the construction requires no division by two."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("compose"),
                DeclarationHandle.Create(Prefix + "StepTwoSignature.compose"),
                H("Chronological composition"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Composition adds degree one and inserts twice the ordered cross term "
                        + "from the left word to the right word at degree two."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("event-signature"),
                DeclarationHandle.Create(Prefix + "eventSignature"),
                H("Single-event signature"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "One event contributes its algebra value at degree one and its square "
                        + "to doubled degree two."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("chronological-signature"),
                DeclarationHandle.Create(Prefix + "chronologicalSignature"),
                H("Chronological word signature"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The signature of a list composes single-event signatures from left to "
                        + "right in operational chronology."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("chen-append"),
                DeclarationHandle.Create(Prefix + "chronological_signature_append"),
                H("Step-two Chen identity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The signature of an earlier word followed by a later word is their "
                        + "chronological signature product."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("degree-one"),
                DeclarationHandle.Create(Prefix + "chronological_signature_degree_one"),
                H("Degree one forgets chronology"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Degree one is the ordinary sum of all observed event values and is "
                        + "therefore insensitive to their order."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("doubled-magnus"),
                DeclarationHandle.Create(Prefix + "doubledMagnusDegreeTwo"),
                H("Doubled degree-two Magnus coordinate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Subtracting the square of degree one from doubled degree two extracts "
                        + "the doubled logarithmic coordinate."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("bch-mul"),
                DeclarationHandle.Create(Prefix + "doubled_magnus_degree_two_mul"),
                H("Degree-two BCH law"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The logarithmic coordinate of a product is the sum of the two "
                        + "coordinates plus the commutator of their degree-one parts."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bch-append"),
                DeclarationHandle.Create(Prefix + "doubled_magnus_degree_two_append"),
                H("Chronological BCH append law"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Combining Chen concatenation with the logarithmic coordinate gives the "
                        + "step-two BCH formula for two event words."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-event-commutator"),
                DeclarationHandle.Create(
                    Prefix + "doubled_magnus_two_events_eq_commutator"),
                H("Two-event Magnus coordinate is the commutator"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a chronology containing exactly two events, the doubled "
                        + "degree-two logarithmic coordinate is their ring commutator."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-event-swap"),
                DeclarationHandle.Create(Prefix + "doubled_magnus_two_events_swap"),
                H("Two-event orientation reversal"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Reversing two events negates the degree-two chronological defect."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("commuting-zero"),
                DeclarationHandle.Create(
                    Prefix + "doubled_magnus_two_events_eq_zero_of_commute"),
                H("Commuting events have zero defect"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A commuting event pair has no degree-two chronological memory."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/HiddenFlow/ProjectionCommutatorIdentity")),
        ]));
}
