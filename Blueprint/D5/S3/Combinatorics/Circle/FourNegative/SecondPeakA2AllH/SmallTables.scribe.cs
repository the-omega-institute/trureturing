using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2AllH;
internal sealed class SmallTablesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Twenty affine families and twenty finite boundary rows", H("Twenty affine families and twenty finite boundary rows"),
        Blocks(
            Describe.Lean(DescribeId.Create("secondpeaka2allh-smalltables-affine-first-identity"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2AllH/SmallTables.affine_first_identity"),
                H("affine first identity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("A consumed part of twenty affine families and twenty finite boundary rows. The complete module scope and assumptions are stated below."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("secondpeaka2allh-smalltables-affine-small-data"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2AllH/SmallTables.affine_small_data"),
                H("affine small data"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("A consumed part of twenty affine families and twenty finite boundary rows. The complete module scope and assumptions are stated below."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("secondpeaka2allh-smalltables-affine-small-bounds"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2AllH/SmallTables.affine_small_bounds"),
                H("affine small bounds"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("A consumed part of twenty affine families and twenty finite boundary rows. The complete module scope and assumptions are stated below."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("secondpeaka2allh-smalltables-affine-small-selection"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2AllH/SmallTables.affine_small_selection"),
                H("affine small selection"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("A consumed part of twenty affine families and twenty finite boundary rows. The complete module scope and assumptions are stated below."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("secondpeaka2allh-smalltables-h4-small-bounds"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2AllH/SmallTables.h4_small_bounds"),
                H("h4 small bounds"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("A consumed part of twenty affine families and twenty finite boundary rows. The complete module scope and assumptions are stated below."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("secondpeaka2allh-smalltables-h4-small-bits"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2AllH/SmallTables.h4_small_bits"),
                H("h4 small bits"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("A consumed part of twenty affine families and twenty finite boundary rows. The complete module scope and assumptions are stated below."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("secondpeaka2allh-smalltables-small-row-pairs"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2AllH/SmallTables.small_row_pairs"),
                H("small row pairs"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("A consumed part of twenty affine families and twenty finite boundary rows. The complete module scope and assumptions are stated below."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("secondpeaka2allh-smalltables-h4-pairs"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2AllH/SmallTables.h4_pairs"),
                H("h4 pairs"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("A consumed part of twenty affine families and twenty finite boundary rows. The complete module scope and assumptions are stated below."))), DescribeRole.Theorem),
            Paragraph(Text("The twenty affine rows cover p in {4,8,16,32} and q in {2,4,8,16,32}. At h=8u each row chooses constant v, m=ju and M=8uC-1. For each of the four first slacks, affine_first_identity proves the exact identity slack=atOne+(u-1)*slope for every integer u. All eighty identities are ring equalities, and every atOne and slope is nonnegative.")),
            Paragraph(Text("The coefficient and stock checks imply the full paired rowBounds for every integer u>=1. Only the bit proof requires u=2^(H-3): j<8 implies ju<2^H and C>=2 gives the proper predecessor submask. The h=4 sector uses exactly twenty explicit natural rows and finite kernel checks of all original old/new bounds, stocks and bit inclusion. The row-pair lemmas connect each table index to the same p,q pair."))), []));
}
