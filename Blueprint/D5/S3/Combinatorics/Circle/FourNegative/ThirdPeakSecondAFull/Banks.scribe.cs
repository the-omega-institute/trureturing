using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakSecondAFull;
internal sealed class BanksDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Third peak second A full cone: Banks", H("Banks"),
        Blocks(Paragraph(Text("The bank words are literal lists of physical labels. A1 and A2 use complement V(h-1), full W, V(h-H), complement or f-masked X, full U, and the remaining V/X masks. B0 and B1 use m=j-1, R=qj, f=3x/(4t), and both B1 delta branches: delta=1 when R<xy, delta=R/(xy) otherwise, including equality. C uses terminal order X,W,V,U and the first positive X insertion location. Every mask partition is proved on actual bit indices and every negative terminal is the physical label d-1,d+c-1,d+c+b-1,k-1.")),
            Describe.Lean(DescribeId.Create("third-peak-second-a-inventory"), DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakSecondAFull.Banks.inventory"), H("inventory"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("private theorem inventory (a b c d : Nat) (hb : 2<=b) (hba : b<a) (hac : a<c) (hd : 2<=d) (hda : d<a) : (bankWord a b c d).Perm (List.range (size a b c d))"))), DescribeRole.Theorem)), []));
}
