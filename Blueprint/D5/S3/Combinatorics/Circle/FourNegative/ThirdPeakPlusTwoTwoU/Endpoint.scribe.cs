using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPlusTwoTwoU;
internal sealed class EndpointDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Third peak plus two: complete original physical construction",
        H("Every original (a,b,d+2,d), 2<=b<a, with a+3<=d or b=2 and d=a+2"),
        Blocks(Describe.Lean(DescribeId.Create("thirdpeakplustwotwou-joint-lift"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakPlusTwoTwoU/Endpoint.actualSource_third_peak_plus_two_two_U_joint_lift"),
            H("The original physical joint lift"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(
                    Paragraph(Text("Let k=a+b+(d+2)+d and s=1+2^a+2^(a+b)+2^(a+b+d+2). The construction uses all original Fin k physical labels, the unchanged seed s, and a cut j<k whose old label is nX=k-1. The earWord inserts the literal fresh label k immediately before nX. Both full OriginalOrder predicates hold on the old and new scalars.")),
                    Paragraph(Text("For each scalar separately all natural finite repetitions m and take lengths n satisfy the original strip bounds, including zero and overlong takes. Both complete repeated words have total zero independently. No finite positive table is used as an unbounded proof.")),
                    Paragraph(Text("Write x=2^a,y=2^b,t=2^d. The general region has y>=4,x>=2y,t>=8x. Exact shifted polynomial certificates prove all first two scalar windows for U masks 0,1,2. A positive integer ceiling selects v, then the first successful branch among (u,v)=(0,v0),(1,v0+3),(2,v0+6). Only the selected branch is required to have nonnegative D; no lower window is asserted for an unused later candidate.")),
                    Paragraph(Text("The boundary b=2,d=a+2 retains all four exponent classes modulo four. Actual powers modulo five and exact natural division produce the physical V mask. Complementary chamberLabels partition the original U and V banks; full W and X retain their original labels. Native old/new packet masses and all terminal windows establish scalar strip bounds. The literal insertion and range preserving label lift give the same witnesses for both full orders.")),
                    Paragraph(Text("The arithmetic window lemmas supply the integer selector, whose masks determine the complementary physical banks. The physical-word theorem uses their exact inventory and old/new masses to prove both scalar strips; the joint lift then transports zero totals to every finite repetition. This construction covers exactly the stated original gap family. No claim of literature novelty is made. The unrestricted Circle problem remains open."))), DescribeRole.Theorem)), []));
}
