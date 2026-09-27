using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class CrownOrderPolytopeDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/lundstrom2025crown");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite exposed faces from active affine slacks.",
        H("Actual crown order polytopes"),
        Blocks(
            Paragraph(Text("The general active-slack argument is the implementation foundation for the classical geometric correspondence used in source Section 2 and Theorem 3.1; it is not claimed as new convex geometry.")),
            Describe.Lean(
                DescribeId.Create("exposed-eq-active-of-finite-slacks"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Geometry/CrownOrderPolytope.exposed_eq_active_of_finite_slacks"),
                H("Active inequalities determine an exposed face"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For a finite family of real affine slacks on a finite-dimensional coordinate space, every exposed face containing an anchor is exactly the feasible points on which all slacks tight throughout that face vanish. The proof constructs a relative interior center by averaging finitely many witnesses and extends feasible segments through it. This is the geometric foundation for the crown face correspondence."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-crown-exposed-faces"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Geometry/CrownOrderPolytope.finite_crown_exposed_faces"),
                H("Finitely many actual exposed faces"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For every natural n, the exposed faces of the crown order polytope form a finite type. Faces are determined by subsets of its finite inequality family. The carrier is a set of real coordinate vectors with bounds zero and one and the alternating crown order inequalities; no combinatorial face-count formula is assumed."))),
                DescribeRole.Theorem))));
}
