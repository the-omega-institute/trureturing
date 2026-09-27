using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class CrownOrderPolytopeFaceCountsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/lundstrom2025crown");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The enumeration counts real exposed faces by affine dimension.",
        H("Actual geometric face counts"),
        Blocks(
            Paragraph(Text("The count has the geometric meaning of source Section 2; the formula is Theorem 3.6. The signed lower binomial index is implemented by an explicit zero guard before natural subtraction.")),
            Describe.Lean(
                DescribeId.Create("crown-geometric-face-count"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Geometry/CrownOrderPolytopeFaceCounts.crownGeometricFaceCount"),
                H("Geometric definition of the count"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For natural n and d, the count is the natural cardinality of actual nonempty exposed faces of the real crown order polytope whose affine-span direction has real dimension d. This definition is independent of the enumerative sum."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("crown-geometric-face-count-eq"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Geometry/CrownOrderPolytopeFaceCounts.crownGeometricFaceCount_eq"),
                H("The face formula for n at least two"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For every n at least two and every natural dimension d, the geometric count equals the exact selected-block sum with two additional vertices and one additional edge. The proof uses the face/partition correspondence, its affine dimension formula, endpoint recovery, parity-profile counts and the exceptional partitions. This formalizes the published face-count formula rather than assuming it."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Geometry/CrownOrderPolytopeSelectionCounts")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Geometry/CrownOrderPolytopeTwoExceptions")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Geometry/CrownOrderPolytopeDimension"))
        ]));
}
