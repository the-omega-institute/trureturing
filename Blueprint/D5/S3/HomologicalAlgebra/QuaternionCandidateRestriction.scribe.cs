using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra;

internal sealed class BarnesWallQuaternionCandidateRestrictionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The quaternion restriction of the split quadratic candidate",
        H("The quaternion restriction distinguishes the two candidates"),
        Blocks(Describe.Lean(
            DescribeId.Create("barnes-wall-quaternion-candidate-restriction"),
            DeclarationHandle.Create(
                "D5/S3/HomologicalAlgebra/QuaternionCandidateRestriction.unique_candidate_after_involution_tests"),
            H("Involution tests determine a unique cohomology bit"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/VertexAlgebra/keller2026barneswall")),
            Blocks(Paragraph(Text(
                "Two hyperbolic pairs support an embedded quaternion group in the split sign " +
                "extension. The nonzero candidate restricts to the cochain detected by the " +
                "quaternion bar cycle. Its restriction therefore distinguishes it from zero."))),
            DescribeRole.Theorem))));
}
