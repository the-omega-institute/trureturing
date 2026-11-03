using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD;
internal sealed class EndpointDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Endpoint", H("Endpoint"),
        Blocks(Paragraph(Text("For every natural 3<=a<c, c+2<=d and d<b, the original seed 1+2^a+2^(a+b)+2^(a+b+c) admits both original orders with a literal fresh ear at cut zero or immediately after nX. Every physical label occurs once. Separate zero period sums transport both strips to every natural repetition and every natural take, including zero and overlong takes. The key connection is between cyclic source arithmetic and physical packet mass: the same binary submask allocation controls both centered source systems, while inserting one fresh label changes the charge without changing the old label order. This completes this HighD domain; a=2 and the whole Circle problem remain separate.")),
            Describe.Lean(DescribeId.Create("highd-endpoint-actualsource-second-peak-high-d-joint-lift"), DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/Endpoint.actualSource_second_peak_high_d_joint_lift"), H("actualSource_second_peak_high_d_joint_lift"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Consumed by the full HighD construction with the exact Lean telescope."))), DescribeRole.Theorem)), []));
}
