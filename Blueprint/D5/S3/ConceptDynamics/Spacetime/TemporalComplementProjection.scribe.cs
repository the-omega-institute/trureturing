using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Spacetime;

internal sealed class TemporalComplementProjectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Temporal composition transports event complements componentwise and preserves the induced signed-charge projection.",
        H("Temporal Complement Projection"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("temporal-complement-projection-selection"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Spacetime/TemporalComplementProjection.complement_selection_projection"),
                H("Complement of a temporal selection projects to component complements"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a guarded temporal composition of contexts c and e, and selections a and b, " +
                    "the complement in the joined current region is exactly the disjoint sum of c's " +
                    "complement of a and e's complement of b, transported by the canonical event equivalence. " +
                    "This is a finite event-set identity and does not assert coverage of the broader temporal-profile atom."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("temporal-complement-projection-readout"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Spacetime/TemporalComplementProjection.temporal_complement_projection"),
                H("Signed charge projects through temporal complement"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The readout of the joined complement equals the sum of the two component complement readouts. " +
                    "The equality follows for arbitrary finite contexts from the componentwise set projection and " +
                    "the finite charge decomposition."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("temporal-complement-projection-spec"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Spacetime/TemporalComplementProjection.temporal_complement_projection_spec"),
                H("Projection and discrete temporal separation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The packaged projection also records the integer one-step gap forced by the strict " +
                    "archive-time guard for every left and right archived event. This arithmetic consequence " +
                    "is part of the module's content witness."))),
                DescribeRole.Theorem))));
}
