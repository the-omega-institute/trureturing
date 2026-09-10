using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Spacetime;

internal sealed class IntegerRepresentativesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Spacetime/IntegerRepresentatives.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The fixed HF names form a canonical balanced archive in every dimension; the source uses dimension three.",
        H("Canonical Integer Representatives"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("integer-representative-event-names"),
                DeclarationHandle.Create(Prefix + "eventNames"),
                H("Signed integer archives use exact HF pair names"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For n, the archive is exactly the Kuratowski pair of each natural index below "
                        + "natAbs n with each fixed positive or negative sign code. The source leaf "
                        + "label is the same index. Time and every Fin d coordinate are zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("integer-representative-index-equivalence"),
                DeclarationHandle.Create(Prefix + "eventEquiv"),
                H("Typed finite indices name precisely the HF archive"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The finite product Fin (natAbs n) times Bool is bijective with the subtype of "
                        + "the exact HF event-name set. Pair and sign injectivity make this a faithful "
                        + "presentation of the prescribed names."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("integer-representative-selection-characterization"),
                DeclarationHandle.Create(Prefix + "representative_selection_positive_iff"),
                H("Positive representatives select exactly positive names"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "When n is positive, the selected subtype is precisely the positive-name image; "
                        + "the negative case has the analogous characterization. Zero selects no event."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("integer-representative-cardinalities"),
                DeclarationHandle.Create(Prefix + "representative_archive_card"),
                H("Canonical archives have twice the absolute integer size"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The archive has cardinality 2 times natAbs n in every dimension."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("integer-representative-current-cardinality"),
                DeclarationHandle.Create(Prefix + "representative_current_card"),
                H("The entire archive is current"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The current region also has cardinality 2 times natAbs n."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("integer-representative-selected-cardinality"),
                DeclarationHandle.Create(Prefix + "representative_selected_card"),
                H("Selection has the absolute integer size"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The sign-selected subset has cardinality natAbs n."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("integer-representative-readout"),
                DeclarationHandle.Create(Prefix + "representative_readout"),
                H("Canonical signed selections read out to their integer"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every event contributes the fixed sign one or minus one. Summing the selected "
                        + "positive or negative names gives exactly n, and summing both signs over the "
                        + "current archive gives zero background charge."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("integer-representative-zero"),
                DeclarationHandle.Create(Prefix + "representative_zero_empty"),
                H("The zero representative is empty"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The zero representative has empty archive, current region and selection in every dimension."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("integer-representative-unit"),
                DeclarationHandle.Create(Prefix + "U"),
                H("U denotes the literal representative of one"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "U is defined as representative 3 1. The notation i(n) denotes representative 3 n, "
                        + "and emptyRepresentative is representative 3 0. Specializing representative_archive_card "
                        + "and representative_current_card at d=3,n=1 gives size two; specializing "
                        + "representative_selected_card gives size one. These are applications of the "
                        + "general theorems. The source positions are Fin 3 to Int, and consumers in dimension "
                        + "three use representative 3 n and the same general theorems."))),
                DescribeRole.Definition)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/History/Spacetime/HFEncoding")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/History/Spacetime/IntegerEncoding")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/History/Spacetime/CoordinateEncoding")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/History/Spacetime/SourceTreeEncoding")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/ConceptDynamics/Spacetime/ComplementCharge"))
        ]));
}
