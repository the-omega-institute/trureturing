using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class MiuraSlabExtremaDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/MiuraSlabExtrema.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Extrema forced by the boundary signs of actual rectangular intervals.", H("Slab extrema in unit-edge height arrays"),
        Blocks(
            Describe.Lean(DescribeId.Create("miuraslabextrema-interval"),
                DeclarationHandle.Create(Prefix + "Interval"), H("Coordinate intervals"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A coordinate interval consists of two actual finite grid coordinates in increasing order. Its first and last coordinates may be physical endpoints."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("miuraslabextrema-rectangle"),
                DeclarationHandle.Create(Prefix + "rectangle"), H("The actual rectangle"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The rectangle is the Cartesian product of the two closed coordinate intervals. Its vertices remain vertices of the original array."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("miuraslabextrema-rowoutward"),
                DeclarationHandle.Create(Prefix + "RowOutward"), H("Vertical boundary signs"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every existing adjacent edge from a row in the interval to a row outside it changes the original height by the specified integer. At a physical boundary there is no extra edge."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("miuraslabextrema-coloutward"),
                DeclarationHandle.Create(Prefix + "ColOutward"), H("Horizontal boundary signs"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every existing adjacent edge from a column in the interval to a column outside it has the specified height change in the same array."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("miuraslabextrema-matching-minimum"),
                DeclarationHandle.Create(Prefix + "matching_minimum"), H("Matching minimum types force an ambient minimum"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every integer unit-edge array and every nonempty row and column interval, if every existing outward vertical and horizontal edge increases height by one, their rectangle contains a strict local minimum of the whole array. A lowest rectangle vertex has higher neighbours inside by the unit-edge law and higher neighbours outside by the two boundary conditions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuraslabextrema-matching-maximum"),
                DeclarationHandle.Create(Prefix + "matching_maximum"), H("Matching maximum types force an ambient maximum"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every integer unit-edge array and every nonempty row and column interval, if every existing outward vertical and horizontal edge decreases height by one, their rectangle contains a strict local maximum of the whole array. This follows by applying the minimum result to the negated actual heights."))), DescribeRole.Theorem))));
}
