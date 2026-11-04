using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail;
internal sealed class EndpointDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Second peak, equal-tail: complete dyadic-mask joint lift",
        H("Every natural 2<=a<c<b with c=d"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-source-second-peak-equal-tail-joint-lift"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualTail/Endpoint.actualSource_second_peak_equal_tail_joint_lift"),
                H("One original permutation and one literal fresh insertion"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every natural a,b,c with 2<=a<c<b and the original equal tail c=d, put k=a+b+c+c and A=1+2^a+2^(a+b)+2^(a+b+c). The theorem supplies a permutation sigma of every original Fin k label and a cut j<=k. Both OriginalOrder(k,A,sigma) and OriginalOrder(k+1,2A,earWord(k,sigma,j)) hold with the unchanged actualSource family.")),
                    Paragraph(Text("The selector is unbounded in r=c-a and t=b-c-1. It chooses alpha,m0,v,j0 and an early Boolean branch from six polynomially certified windows. The physical masks use T_s(m)=s(m+1)-1, preserve sparse submask containment and partition every W bank, including the sole small tuple (a,c,b)=(2,3,4).")),
                    Paragraph(Text("Both original orders retain every physical occurrence exactly once. The fresh label is inserted literally in either of the two selector modes; no source relabeling, rotation or finite feasibility assumption is used. The endpoint also records every natural repeated prefix and take, including zero repetitions and overlong prefixes, together with separate zero totals for the old and fresh words.")),
                    Paragraph(Text("The proof reuses PacketNormalForm source values, terminal masses and zero-period transport. The old bound is modulus(k)/2 and the new bound is modulus(k); the identity modulus(k+1)/2=modulus(k) transfers the new repeated-prefix result. This is the complete second-peak equal-tail face and leaves the unchanged wholeCircle J/C3.1 objective open."))),
                DescribeRole.Theorem)), []));
}
