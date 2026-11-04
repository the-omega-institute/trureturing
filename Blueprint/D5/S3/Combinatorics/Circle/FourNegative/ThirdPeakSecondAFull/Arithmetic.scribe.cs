using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakSecondAFull;
internal sealed class ArithmeticDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Third peak second A full cone: Arithmetic", H("Arithmetic"),
        Blocks(Paragraph(Text("The arithmetic source proves the first V seam, both A seams, the shared A2/B third seam, both B second seams, and all three C seams. The B1 proof uses the exact identities 52--55 with delta=1 for R<xy and delta=R/(xy) for R>=xy, including equality. Positive bases are F, B, K-(t-1)F, and C-2q. The three small A2 tuples are discharged by their literal certificates.")),
            Describe.Lean(DescribeId.Create("third-peak-second-a-windows"), DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakSecondAFull.Arithmetic.all_windows"), H("all_windows"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("private theorem all_windows (a b c d : Nat) (hb : 2<=b) (hba : b<a) (hac : a<c) (hd : 2<=d) (hda : d<a) : exact branch window conjunctions"))), DescribeRole.Theorem)), []));
}
