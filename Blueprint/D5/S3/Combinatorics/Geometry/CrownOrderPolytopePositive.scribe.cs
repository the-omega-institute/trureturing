using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class CrownOrderPolytopePositiveDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/lundstrom2025crown");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual two-vertex triangle completes the geometric formula.",
        H("All positive crown sizes"),
        Blocks(
            Paragraph(Text("The full-vector convention is the source Section 2 convention. The positive-size theorem completes the separate n equals one boundary, where the source cycle picture degenerates to a chain.")),
            Describe.Lean(
                DescribeId.Create("crown-geometric-fvector"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Geometry/CrownOrderPolytopePositive.crownGeometricFVector"),
                H("The full geometric f-vector"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For n, the vector has 2n+2 entries indexed by Fin(2n+2). Entry zero is one for the empty face; entry k greater than zero is the actual geometric count in dimension k-1. Its last entry includes the whole polytope."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("crown-geometric-face-count-eq-of-pos"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Geometry/CrownOrderPolytopePositive.crownGeometricFaceCount_eq_of_pos"),
                H("The formula for every positive size"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For every positive n and every natural dimension d, the same exact geometric face-count formula holds. At n equals one the augmented crown is a chain, and its actual faces are counted by consecutive cuts. This proves the triangle boundary independently of the n at least two cycle arguments."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Geometry/CrownOrderPolytopeFaceCounts"))
        ]));
}
