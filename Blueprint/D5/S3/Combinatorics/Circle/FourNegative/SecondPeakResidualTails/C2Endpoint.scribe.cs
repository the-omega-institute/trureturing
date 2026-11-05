using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails;
internal sealed class C2EndpointDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Physical c=2 residual construction", H("Physical c=2 residual construction"),
        Blocks(
            Describe.Lean(DescribeId.Create("c2-physical-gates"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/SecondPeakResidualTails/C2Endpoint.c2_physical_gates"),
                H("c2_physical_gates"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For a=3,c=2,d>=4 and b>d, the original scalar banks are identified with actual centered sources and physical masses. The exceptional e=d-3=4 keeps [2,3,0,1]. Signed terminal divisions and fresh OLD A are separate. The actual physical lower and upper sides feed the common Completion. The original 632-line preparation is superseded by this consolidated construction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actualSource-c2-residual-joint-lift"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/SecondPeakResidualTails/C2Endpoint.actualSource_c2_residual_joint_lift"),
                H("actualSource_c2_residual_joint_lift"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For a=3,c=2,d>=4 and b>d, the original scalar banks are identified with actual centered sources and physical masses. The exceptional e=d-3=4 keeps [2,3,0,1]. Signed terminal divisions and fresh OLD A are separate. The actual physical lower and upper sides feed the common Completion. The original 632-line preparation is superseded by this consolidated construction."))),
                DescribeRole.Theorem)), []));
}
