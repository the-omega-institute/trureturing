using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.SourceReconstruction;

internal sealed class SourceEvaluatorDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite original two-word source evaluation",
        H("Finite original two-word source evaluation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sourcereconstruction-sourceevaluator-groundWord-agrees"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/SourceReconstruction/SourceEvaluator.groundWord_agrees"),
                H("Charged ground evaluation on every target word"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The original SC recurrence moves each negative current through the original charged-ground mode. The base is the literal actualField ground-ground coefficient. Recursion is on the complete finite target occurrence word, with no occupation cutoff."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sourcereconstruction-sourceevaluator-source-insertion-finite"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/SourceReconstruction/SourceEvaluator.source_insertion_finite"),
                H("An explicit finite SI range"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The existing smaller-source field order and the original target current bound produce a common finite range. Both unweighted insertion terms vanish outside it."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sourcereconstruction-sourceevaluator-sourceWord-agrees"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/SourceReconstruction/SourceEvaluator.sourceWord_agrees"),
                H("Source-word recursion from SI and SC"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The original SI recurrence shortens the left occurrence word. Every right target is still an arbitrary original state. The empty left word uses the charged-target-word evaluator, extended by the finite original target expansion."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sourcereconstruction-sourceevaluator-evaluate-agrees"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/SourceReconstruction/SourceEvaluator.evaluate_agrees"),
                H("Every original source mode is reconstructed"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("Finite original source expansion extends the two-word evaluation to arbitrary original source and target states and every integer mode. This evaluator concerns the already proved original untwisted source VOA, not the unavailable native charged both-sheet iterate."))),
                DescribeRole.Theorem))));
}
