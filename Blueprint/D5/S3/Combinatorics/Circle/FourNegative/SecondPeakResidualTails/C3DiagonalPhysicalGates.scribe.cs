using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails;
internal sealed class C3DiagonalPhysicalGatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original physical gate transport", H("Original physical gate transport"),
        Blocks(
            Describe.Lean(DescribeId.Create("c3-diagonal-physical-gates"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/SecondPeakResidualTails/C3DiagonalPhysicalGates.c3_diagonal_physical_gates"),
                H("c3_diagonal_physical_gates"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The c=3,a=5,d>=7 cone and the c>=3,a=c+1,d>=2c cone retain b>d and the same actual physical banks. The original PacketNormalForm.chain_values supplies signed terminal quotients; parity transports them to doubled values. Original physical_masses identifies actual Finset sums with the symbolic coefficients. Both complete telescopes vanish. The matched-new old-label total is -A and the separate fresh value is A; the complete new total is zero. This establishes old lower and new upper sides for Completion."))),
                DescribeRole.Theorem)), []));
}
