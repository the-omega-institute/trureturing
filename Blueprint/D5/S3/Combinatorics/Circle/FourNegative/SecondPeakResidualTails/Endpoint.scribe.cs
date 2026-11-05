using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails;
internal sealed class EndpointDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete original residual physical joint lift", H("Complete original residual physical joint lift"),
        Blocks(
            Describe.Lean(DescribeId.Create("actualSource-residual-joint-lift"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/SecondPeakResidualTails/Endpoint.actualSource_residual_joint_lift"),
                H("actualSource_residual_joint_lift"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For b>d and exactly one of (c=2,a=3,d>=4), (c>=3,a=c+1,d>=2c), or (c=3,a=5,d>=7), the theorem constructs one sigma whose natural labels are exactly physicalWord(residualBanks,residualOrder). Literal cut0 is zero. Both complete OriginalOrder clauses hold for A=1+2^a+2^(a+b)+2^(a+b+c) and 2A. On inherited labels the new total is -A; the fresh label has value A. Every natural repeated/taken prefix has its distinct old N/2 or new N bound, and both repeated totals are zero. The construction discharges every physical-side assumption. This is the residual domain alone; unrestricted Circle J and official acceptance remain open."))),
                DescribeRole.Theorem)), []));
}
