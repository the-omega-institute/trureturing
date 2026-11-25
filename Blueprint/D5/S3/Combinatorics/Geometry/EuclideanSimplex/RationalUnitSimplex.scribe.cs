using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry.EuclideanSimplex;

internal sealed class RationalUnitSimplexDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/kominers2026rationaledges");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The arithmetic classification of regular simplices on rational unit spheres.",
        H("Regular simplices on rational unit spheres"),
        Blocks(Describe.Lean(DescribeId.Create("rational-unit-simplex"),
            DeclarationHandle.Create(
                "D5/S3/Combinatorics/Geometry/EuclideanSimplex/RationalUnitSimplex.rational_unit_simplex_iff"),
            H("A square criterion for rational regular simplex vertices"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(
                Paragraph(Text(
                    "Let n be positive. The rational unit sphere in n coordinates contains n+1 "
                    + "distinct points with a common pairwise inner product if and only if the odd "
                    + "member of the pair n, n+1 is a square. This is the unit-circumradius "
                    + "specialization of Kominers's squared-edge-length classification.")),
                Paragraph(Text(
                    "The square Gram matrix of all n+1 points is singular, forcing the common "
                    + "off-diagonal entry to be minus one divided by n. The Gram determinant of "
                    + "the first n columns is a rational square. Removing square factors gives "
                    + "the parity-dependent condition.")),
                Paragraph(Text(
                    "Center the coordinate basis in n+1 dimensions. For odd square n, a rational "
                    + "similarity on pairs of coordinates gives the required lengths. For even n "
                    + "with n+1 square, n is divisible by four and the all-ones normal can be "
                    + "normalized rationally. Quaternion multiplication on blocks of four "
                    + "coordinates supplies the remaining similarity. A rational reflection "
                    + "takes the unit normal to a coordinate axis, which can then be dropped."))),
            DescribeRole.Theorem))));
}
