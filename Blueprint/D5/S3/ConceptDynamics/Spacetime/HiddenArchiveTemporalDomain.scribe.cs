using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Spacetime;

internal sealed class HiddenArchiveTemporalDomainDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Spacetime/HiddenArchiveTemporalDomain.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An inactive archived occurrence preserves every current attribute and both spatial charges, "
            + "while changing the domain of temporal composition.",
        H("Hidden Archive and Temporal Domain"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("double-spatial-readout"),
                DeclarationHandle.Create(Prefix + "pi"),
                H("The spatial readout has two finite-support coordinates"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The first coordinate sums signed point masses over the entire current region. "
                        + "The second sums them over the selected occurrences. Each mass is placed "
                        + "at the event's actual integer spatial position."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("inactive-extension"),
                DeclarationHandle.Create(Prefix + "U_old"),
                H("One new occurrence extends the literal archive of U"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "U is the canonical representative of one in dimension three. The extended "
                        + "archive inserts exactly the fresh HF name eventName 1 true. Its time is "
                        + "two, its position is zero, its sign is positive and its source is leaf nine. "
                        + "Causality remains empty. The current and selected occurrences retain "
                        + "their HF names and all their attributes, including time and source."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("projection-domain-claim"),
                DeclarationHandle.Create(Prefix + "CurrentSpatialProjectionPreservesTemporalDomains"),
                H("A universal temporal-domain preservation claim"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The claim quantifies over all balanced rich representations in dimension "
                        + "three and every fixed balanced right operand. It asserts that equal "
                        + "double spatial readouts give equivalent full-archive temporal guards."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hidden-archive-witness"),
                DeclarationHandle.Create(Prefix + "hidden_archive_preserves_current_changes_temporal_domain"),
                H("Unchanged current data coexist with different temporal domains"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The theorem supplies an archive embedding that is the identity on HF names, "
                        + "literal equality of current and selected name sets, and equality of all "
                        + "current attributes. The added occurrence lies in neither current set nor "
                        + "selection. Both representations are balanced and have spatial readout "
                        + "zero paired with the unit point mass at zero. Fixing the right operand "
                        + "to the time-one shift of U, composition with U is legal and reads two. "
                        + "The explicit time-two added event and time-one right event violate the "
                        + "extended archive's guard. Temporal composition requires a guard proof, "
                        + "so the illegal branch has no assigned output."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("projection-domain-refutation"),
                DeclarationHandle.Create(Prefix + "current_spatial_projection_domain_refutation"),
                H("Spatial projection does not preserve temporal-composition domains"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Applying the universal claim to the complete witness contradicts its failed "
                        + "full-archive guard. Retaining all current event times also fails to "
                        + "recover this domain difference."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/ConceptDynamics/Spacetime/IntegerRepresentatives")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/ConceptDynamics/Spacetime/TemporalComposition"))
        ]));
}
