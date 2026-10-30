using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle;

internal sealed class TwoNegativeJointLiftDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native common-cut two-negative joint lift",
        H("Native common-cut two-negative joint lift"),
        Blocks(
            Describe.Lean(DescribeId.Create("two-negative-joint-lift"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/TwoNegativeJointLift.actualSource_two_negative_joint_lift"),
                H("Native common-cut two-negative joint lift"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every a>b>=2, with k=a+b, q=2^a, r=2^b, N=qr-1 and v=q+1, the actual old source and actual doubled source admit full physical permutations at one shared cut. The selector uses one literal V-ladder support with w=floor((N-v)/(2r+1)); its old mass is (r+1)w and its new mass is (2r+1)w.")),
                    Paragraph(Text("The U and V labels, alpha and beta negatives, and the fresh new label are physical occurrences. The q=2r and q>=4r cases use their stated common-cut orders, and the InStrip proof covers every natural prefix, including empty, full and overlong takes.")),
                    Paragraph(Text("This constructor does not assert nonzero phase transport, a numerical-period quotient, or completion of the full Circle C3.1 problem.")))),
            DescribeRole.Theorem)), []));
}
