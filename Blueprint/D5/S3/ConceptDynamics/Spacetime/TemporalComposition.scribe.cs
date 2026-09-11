using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Spacetime;

internal sealed class TemporalCompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Guarded Temporal Composition.",
        H("Guarded Temporal Composition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("temporalcomposition-hf-time-condition-iff"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Spacetime/TemporalComposition.hf_time_condition_iff"),
                H("The exact temporal guard on HF archives"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every archived left event must occur strictly before every archived right event, "
                    + "including inactive events. This condition is necessary and sufficient for the copied "
                    + "absolute times to increase on the constructed relation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("temporalcomposition-q-temporal"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Spacetime/TemporalComposition.q_temporal"),
                H("The guarded operation adds readouts"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The relation adds every old-left to old-right edge and is transitive and irreflexive. "
                    + "The operation preserves absolute times, adds selected and background charges, and "
                    + "preserves balance on its declared domain."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("temporalcomposition-guard-of-large-shift"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Spacetime/TemporalComposition.guard_of_large_shift"),
                H("An explicit input translation makes composition possible"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Translation adds a specified integer to every time in the right input. A finite "
                    + "nonnegative bound gives a sufficiently large shift for any two archives. Empty archives "
                    + "satisfy the guard vacuously; the operation itself performs no translation."))),
                DescribeRole.Theorem))));
}
