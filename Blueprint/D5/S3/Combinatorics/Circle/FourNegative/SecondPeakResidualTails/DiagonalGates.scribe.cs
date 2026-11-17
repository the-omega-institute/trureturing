using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails;
internal sealed class DiagonalGatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Universal doubled gates for a=c+1", H("Universal doubled gates for a=c+1"),
        Blocks(
            Describe.Lean(DescribeId.Create("diagonal-doubled-gates"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/SecondPeakResidualTails/DiagonalGates.diagonal_doubled_gates"),
                H("diagonal_doubled_gates"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For every c>=3 and all natural delta,ell, the original diagonalBanks supply four boundary charts and the selector tail. The tail uses its actual affine dependence on S between 4 and 4(z+1). The terminal order is [0,3,2,1]. The new telescope includes separate fresh 2A and matched-new total -2A. Attribution: uxwv-lowest-diagonal-complement-selector-20261102.py."))),
                DescribeRole.Theorem)), []));
}
