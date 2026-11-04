using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakSecondAFull;
internal sealed class EndpointDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Third peak second A full cone: Endpoint", H("Endpoint"),
        Blocks(Paragraph(Text("For every original natural 2<=b<a<c and 2<=d<a, at k=a+b+c+d and A=1+2^a+2^(a+b)+2^(a+b+c), the theorem supplies one permutation sigma of all k labels and the explicit literal piecewise freshCut with j<k. It proves OriginalOrder k A sigma and OriginalOrder (k+1) (2*A) (earWord k sigma j). Every natural replicate/flatten/take prefix on both actual source orders lies in the required closed strip, and both independently repeated words have zero total for every natural repetition. The Circle J/C3.1 question remains OPEN.")),
            Describe.Lean(DescribeId.Create("actualsource-third-peak-second-a-full-joint-lift"), DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakSecondAFull.actualSource_third_peak_second_a_full_joint_lift"), H("actualSource_third_peak_second_a_full_joint_lift"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("theorem actualSource_third_peak_second_a_full_joint_lift (a b c d : Nat) (hb : 2<=b) (hba : b<a) (hac : a<c) (hd : 2<=d) (hda : d<a) : exact OriginalOrder, all replicate/take bounds, and repeated zero totals"))), DescribeRole.Theorem)), []));
}
