using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakSecondAFull;
internal sealed class BanksDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Third peak second A full cone: Banks", H("Banks"),
        Blocks(Paragraph(Text("The bank words are literal lists of physical labels. A1 and A2 use complement V(h-1), full W, V(h-H), complement or f-masked X, full U, and the remaining V/X masks. B0 and B1 use m=j-1, R=qj, f=3x/(4t), and both B1 delta branches: delta=1 when R<xy, delta=R/(xy) otherwise, including equality. C uses terminal order X,W,V,U and the first positive X insertion location. For nested powers 2^v<=2^u and 0<=delta<2^v, the three masks full XOR (2^u-1), 2^u-2^v+delta, and (2^v-1) XOR delta partition the physical bank. The positive stock omits all four terminal labels d-1,d+c-1,d+c+b-1,k-1. The terminals themselves are separate members of the negative inventory.")),
            Describe.Lean(DescribeId.Create("third-peak-second-a-band-partition"), DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakSecondAFull/Banks.labels_band_split"), H("labels_band_split"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("private theorem labels_band_split (len off u v delta : Nat) (hvu : v<=u) (hdelta : delta<2^v) : exact three-way physical mask partition"))), DescribeRole.Theorem)), []));
}
