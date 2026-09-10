using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Reversal;

internal sealed class VisibleNegationLiftsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/Reversal/VisibleNegationLifts.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All involutive lifts of visible negation are classified by idempotents in the observation kernel.",
        H("Visible Negation Lifts"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("visible-negation-lifts-fixedpart"),
                DeclarationHandle.Create(Prefix + "fixedPart"),
                H("fixedPart"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The existing canonical fixed summand, packaged as a linear map."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("visible-negation-lifts-fixedpart-idempotent"),
                DeclarationHandle.Create(Prefix + "fixedPart_idempotent"),
                H("fixedPart idempotent"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The canonical fixed summand is an idempotent."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("visible-negation-lifts-fixedpart-in-observation-kernel"),
                DeclarationHandle.Create(Prefix + "fixedPart_in_observation_kernel"),
                H("fixedPart in observation kernel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A visible minus sign annihilates the entire fixed summand."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("visible-negation-lifts-visible-negation-iff-hidden-idempotent"),
                DeclarationHandle.Create(Prefix + "visible_negation_iff_hidden_idempotent"),
                H("visible negation iff hidden idempotent"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every involution lifting the observed minus sign has a hidden idempotent representation. The converse constructs the involution law; uniqueness is the separate theorem below."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("visible-negation-lifts-hidden-idempotent-unique"),
                DeclarationHandle.Create(Prefix + "hidden_idempotent_unique"),
                H("hidden idempotent unique"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The hidden idempotent is determined by the full involution, even though it is invisible to the original observation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("visible-negation-lifts-visiblereflection"),
                DeclarationHandle.Create(Prefix + "visibleReflection"),
                H("visibleReflection"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Reverse the retained subspace and preserve the complementary subspace."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("visible-negation-lifts-visiblereflection-spec"),
                DeclarationHandle.Create(Prefix + "visibleReflection_spec"),
                H("visibleReflection spec"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A projection induces a genuine state involution with visible action -I."))),
                DescribeRole.Theorem))));
}
