using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter;
internal sealed class EndpointDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete equal-outer physical face", H("Original labels and exact unbounded domain"),
        Blocks(Describe.Lean(DescribeId.Create("actual-source-third-peak-equal-outer-joint-lift"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakEqualOuter/Endpoint.actualSource_third_peak_equal_outer_joint_lift"),
                H("Complete original physical domain"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every original natural 2<=b<a<c put d=a, k=a+b+c+a and A=1+2^a+2^(a+b)+2^(a+b+c). There exist one permutation sigma of all Fin k labels and j<=k such that the unchanged OriginalOrder(k,A,sigma) and OriginalOrder(k+1,2A,earWord(k,sigma,j)) both hold. The ear inserts exactly the sole fresh label k.")),
                    Paragraph(Text("For every natural m,n, the n-term take of m copies of sigma has actual centered-source sum in [0,modulus(k)/2], and that of m copies of the ear word lies in [0,modulus(k)]. For each m, each repeated row has zero total separately. Zero repetitions and zero or overlong takes are included.")),
                    Paragraph(Text("The exhaustive physical consumer uses c>=a+3, moderate high, moderate near, small A,small B,small C and the sole local 15-label exception. No extra construction hypothesis is added. The existing zero_period_transport supplies all finite repetitions. The unrestricted Circle objective remains open."))), DescribeRole.Theorem)), []));
}
