using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Reversal;

internal sealed class QuadraticObservationClosureDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/Reversal/QuadraticObservationClosure.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Quadratic observed dynamics closes exactly when its hidden linear, hidden quadratic, and mixed terms vanish.",
        H("Quadratic Observation Closure"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("quadratic-observation-closure-vectorfield"),
                DeclarationHandle.Create(Prefix + "vectorField"),
                H("vectorField"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Linear drift minus the diagonal of a genuine bilinear map."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("quadratic-observation-closure-observed-increment"),
                DeclarationHandle.Create(Prefix + "observed_increment"),
                H("observed increment"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact observed increment, including the hidden self-interaction."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("quadratic-observation-closure-quadratic-closure-iff"),
                DeclarationHandle.Create(Prefix + "quadratic_closure_iff"),
                H("quadratic closure iff"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A complete necessary and sufficient condition for exact Markovian closure of a quadratic vector field under a linear projection."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("quadratic-observation-closure-quadratic-fiber-criterion"),
                DeclarationHandle.Create(Prefix + "quadratic_fiber_criterion"),
                H("quadratic fiber criterion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The coefficient criterion is equivalent to the pre-existing answerability condition on all pairs in every observation fiber."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("quadratic-observation-closure-same-visible-negation"),
                DeclarationHandle.Create(Prefix + "same_visible_negation"),
                H("same visible negation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Full and visible-only reversal have the same observed state."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("quadratic-observation-closure-reversal-acceleration-gap"),
                DeclarationHandle.Create(Prefix + "reversal_acceleration_gap"),
                H("reversal acceleration gap"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The surviving mixed term is the exact difference between the two observed accelerations. Linear hidden drift is the only extra hypothesis."))),
                DescribeRole.Theorem))));
}
