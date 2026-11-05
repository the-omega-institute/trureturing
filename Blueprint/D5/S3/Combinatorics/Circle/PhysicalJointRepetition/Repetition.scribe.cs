using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.PhysicalJointRepetition;

internal sealed class RepetitionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit physical-J repetition at a fixed ear cut",
        H("Explicit physical-J repetition at a fixed ear cut"),
        Blocks(
            Describe.Lean(DescribeId.Create("physical-joint-repetition"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/PhysicalJointRepetition/Repetition.physical_joint_repetition"),
                H("Explicit physical-J repetition at a fixed ear cut"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For d>=2, 1<=w<=2^(d-1)-1, r>=2 and cut<=d, a supplied old physical order and its supplied joint ear order produce an explicit descending-block repetition at lengths d*r and d*r+1. Every physical occurrence is retained, and the fresh label is inserted at the same numeric cut in the first block.")),
                    Paragraph(Text("The old row is G*a_i with G=geom(d,r). The charged augmented row is 2*G*a_i-F_j(i), where F_j(i)=2^i*w*geom(d,j)+charge(d,w,i) is nonnegative and has total w*2^(d*j). The top row is R*g_i+H*a_i with R=(2^d)^(r-1), H=geom(d,r-1), and G=R+H. Top prefixes use the supplied old and new strips; lower rows start and end at the geometric heights and remain in the new strip.")),
                    Paragraph(Text("The construction is a substantive charged dynamical transport. Equal numerical values retain distinct physical labels. Unrestricted four-independent-gap J and Circle C3.1 remain open."))),
                DescribeRole.Theorem),
            new DocumentBlock.Section(H("Application boundary"), Blocks(
                Paragraph(Text("The theorem consumes supplied base witnesses and does not construct them. It covers empty, complete and overlong natural prefixes and the endpoint cuts cut=0 and cut=d."))))), []));
}
