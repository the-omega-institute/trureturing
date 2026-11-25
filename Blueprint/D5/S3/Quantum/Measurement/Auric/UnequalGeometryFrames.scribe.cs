using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement.Auric;

internal sealed class UnequalGeometryFramesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fiber-flat realization of rank-capped effects",
        H("Fiber-flat realization of rank-capped effects"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exists-frame-of-input-at-law"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/UnequalGeometryFrames.exists_frame_of_inputAtLaw"),
                H("Effects recovered from a state frame"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("In either branch the frame belongs to P or I − P. Its three fiber row Grams are positive, sum to the identity and have the stated traces and rank caps."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exists-input-at-law-of-feasible"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/UnequalGeometryFrames.exists_inputAtLaw_of_feasible"),
                H("Realization of the entire prescribed triple"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/HilbertOperators/lipoon2003principalsubmatrices"),
                    LibraryNoteRef.Create("D5/L/HilbertOperators/massey2010noncommutativeschurhorn")),
                Blocks(
                    Paragraph(Text("Choose flat factors of the three effects and stack their rows in the actual coordinate fibers. The Gram sum makes the stack isometric. Its projection or complement yields an admissible normalized state and recovers exactly the prescribed effects. Empty fibers and zero working rank are included."))),
                DescribeRole.Theorem))));
}
