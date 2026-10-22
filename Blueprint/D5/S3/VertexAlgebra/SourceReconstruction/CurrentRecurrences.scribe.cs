using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.SourceReconstruction;

internal sealed class CurrentRecurrencesDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual original source current recurrences",
        H("Actual original source current recurrences"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sourcereconstruction-currentrecurrences-insertionFirst-finite"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/SourceReconstruction/CurrentRecurrences.insertionFirst_finite"),
                H("The first source insertion support"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("Original source-field truncation bounds the shifted modes before the binomial coefficient is introduced."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sourcereconstruction-currentrecurrences-insertionSecond-finite"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/SourceReconstruction/CurrentRecurrences.insertionSecond_finite"),
                H("The second source insertion support"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The actual original nonnegative current acts with finite pointwise support on the target. This statement does not rely on binomial zeros."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sourcereconstruction-currentrecurrences-source-insertion"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/SourceReconstruction/CurrentRecurrences.source_insertion"),
                H("SI from the original source iterate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The original source VOA iterate is specialized to the actual basis current at every negative order. The negative generalized binomial and signed phase are normalized explicitly. This is a consumed bind-only interface, not an independent novelty claim: SourceEvaluator.sourceWord_agrees uses it on its live recursive proof path."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sourcereconstruction-currentrecurrences-source-charged-commutation"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/SourceReconstruction/CurrentRecurrences.source_charged_commutation"),
                H("SC from the original source mode commutator"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The original current-ground commutator contracts exactly the zero nonnegative current mode. Every higher mode vanishes on the original charged ground. The resulting identity has the exact negative bilinear correction. This consumed bind-only interface is used by SourceEvaluator.groundWord_agrees."))),
                DescribeRole.Theorem))));
}
