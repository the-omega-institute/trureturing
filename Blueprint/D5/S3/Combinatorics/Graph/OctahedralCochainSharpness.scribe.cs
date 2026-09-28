using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class OctahedralCochainSharpnessDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/OctahedralCochainSharpness.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Four path faces give two antipodal defects and a sharp edge-repair barrier.",
        H("Octahedral cochain sharpness"),
        Blocks(
            Paragraph(Text(
                "The boundary of the four-dimensional cross-polytope has four opposite "
                + "vertex pairs. A tetrahedron chooses one vertex from each pair. A triangle "
                + "omits one pair and chooses one vertex from each remaining pair; faces and "
                + "simplicial edges are unordered and have no repeated vertices.")),
            Describe.Lean(
                DescribeId.Create("tetrahedron-vertices"),
                DeclarationHandle.Create(Prefix + "tetraVertices"),
                H("Tetrahedral vertices"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A four-bit word determines the unordered set of four vertices obtained "
                    + "by taking its bit from each of the four opposite pairs."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("triangle-vertices"),
                DeclarationHandle.Create(Prefix + "triangleVertices"),
                H("Triangular vertices"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A missing coordinate and three remaining bits determine an unordered "
                    + "three-vertex face. Every valid unordered triangle occurs exactly once."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("edge-coboundary"),
                DeclarationHandle.Create(Prefix + "d1"),
                H("Edge coboundary"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The value of d1(e) on a triangle is the sum in F2 of e on its three "
                    + "unordered two-vertex subsets."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("tetrahedral-defect"),
                DeclarationHandle.Create(Prefix + "d2"),
                H("Tetrahedral coboundary"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The value of d2(F) at a tetrahedron is the sum in F2 of the values "
                    + "on its four incident unordered triangles."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cochain-weight"),
                DeclarationHandle.Create(Prefix + "weight"),
                H("Triangular support weight"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The weight of a triangle cochain counts each of the 32 valid triangles "
                    + "once when its value is nonzero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("defect-count"),
                DeclarationHandle.Create(Prefix + "defects"),
                H("Tetrahedral defect count"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The defect count is the number of the 16 tetrahedra on which d2(F) "
                    + "is nonzero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("antipodal-path"),
                DeclarationHandle.Create(Prefix + "path"),
                H("The antipodal path cochain"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The cochain P equals one on the four cube edges in directions 0, 1, 2, "
                    + "and 3 along the path 0000 to 1000 to 1100 to 1110 to 1111, and zero "
                    + "on every other triangle."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("sharp-repair-barrier"),
                DeclarationHandle.Create(Prefix + "antipodal_repair_sharpness"),
                H("Four errors for two antipodal defects"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "There are 16 tetrahedra and 32 triangular coordinate faces. The "
                        + "coordinate-face map is a bijection onto all valid unordered "
                        + "three-vertex faces; every tetrahedron has four vertices, and its "
                        + "four coordinate triangles are subsets of its vertex set.")),
                    Paragraph(Text(
                        "The path cochain P has weight four and defect count two. For every "
                        + "edge cochain e on unordered vertex pairs, the triangle cochain "
                        + "P+d1(e) has weight at least four. Equality is attained by e=0, "
                        + "so the minimum repair weight is four.")),
                    Paragraph(Text(
                        "For each missing coordinate, summing tetrahedral defects on its "
                        + "zero side cancels all internal triangles in F2 and leaves the "
                        + "triangle sum in that direction. Exactly one antipodal defect lies "
                        + "on that side. The four disjoint direction classes therefore each "
                        + "contain an error. The identity d2(d1(e))=0 transfers this argument "
                        + "to every edge repair."))),
                DescribeRole.Theorem))));
}
