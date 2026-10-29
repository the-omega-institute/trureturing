using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle;

internal sealed class TwoSmallPlacementDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Placing two SMALL occurrences across two free gaps",
        H("Placing two SMALL occurrences across two free gaps"),
        Blocks(
            Paragraph(Text("The physical source is centered modulo N=2^k-1. A label is SMALL when its absolute increment is less than Q=2^(k-2); all other labels are LARGE. Physical occurrences are counted even when their numerical values coincide.")),
            Describe.Lean(DescribeId.Create("even-cut"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/TwoSmallPlacement.even_cut"),
                H("The cut forced by the two even gap lengths"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Write the even gaps as 2p and 2q with p<=q and p+q>=1. Set a=4^p, b=4^q, h=q-p-1 in natural subtraction and v=4^h. Then h<q. If p=q, a=b and v=1. Otherwise b=4av. Thus the cut is calculated from the source gap lengths."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("even-placement"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/TwoSmallPlacement.even_placement"),
                H("The complete even-gap placement"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The arithmetic function f records three times each actual increment. Assume its SMALL values are f(0)=C-b and f(2p+1)=C-a, and its two LARGE arcs have the actual period-closing pair formulas, where N=4ab-1 and C=2ab-1. The constructed word is [2p+1] followed by [1..2p], then [2p+2..2p+1+2h], then [0], then the remaining second arc. It is a permutation of every natural physical position below 2p+2q+2, has total zero, and every prefix lies between zero and 3C. Deleting precisely positions 0 and 2p+1 yields List.range'(1,2p) appended to List.range'(2p+2,2q), with their forward physical order intact. The first SMALL occurrence starts at height C-a. The first arc and the first h second-arc pairs lose alpha(4^i-1) and beta(4^j-1), with alpha=2b+1 and beta=2a+1. Their final height T=2b+1-beta*v is nonnegative: it is zero for equal gaps and equals (6a-1)v+1 otherwise. Their peaks are at most C-a+N<=3C. Inserting the actual label zero raises the height to beta(b-v). Remaining pair endpoints are beta(b-4^j), and their peaks are N+beta*b-2beta*4^j. The calculated cut implies b+2<=2beta*v, giving the upper bound for every remaining peak. A consecutive-pair induction checks the intermediate step and both endpoints, and concatenation checks each SMALL separately. Physical range identities prove the full permutation, including empty gaps and repeated numerical values."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("odd-placement"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/TwoSmallPlacement.odd_placement"),
                H("The complete odd-gap seam"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For gaps 2p+1 and 2q+1, set a=2*4^p, b=2*4^q, N=4ab-1 and C=2ab-1. The scaled SMALL values are f(0)=C+b and f(2p+2)=-(C+a). Use the entire first LARGE arc, then the actual labels [2p+2,0], then the entire second LARGE arc. No comparison of p and q is needed. The first-arc pair endpoints are D(4^i-1), with D=2b-1, and its peaks are N-D+2D4^i. Its final height is F=3(C+1)-(a+2b)<=3C. The first SMALL step reaches exactly (2a-1)(2b-1)>=0; the second reaches H=3(C+1)-(2a+b)<=3C. Second-arc heights before negative steps are N+(2a-1)b-(2a-1)4^j. Their following valleys are (2a-1)(b-2*4^j), which are nonnegative and finish at zero because b=2*4^q. This proves every individual prefix and the full physical permutation. Deleting precisely positions 0 and 2p+2 yields List.range'(1,2p+1) appended to List.range'(2p+3,2q+1), in forward physical order."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("unscale-strip"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/TwoSmallPlacement.unscale_strip"),
                H("Removing the factor three"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An integer word bounded between zero and 3C under increments 3f is bounded between zero and C under f. The statement also allows any initial height h, scaled to 3h. This transfers the exact integer arithmetic to the original source increments without rational labels."))),
                DescribeRole.Theorem),
            Paragraph(Text("The mathematical source context is Damasdi, Frankl, Pach and Palvolgyi, Monochromatic configurations on a circle, arXiv:2504.10687v2, Conjecture 3.1, DOI 10.5070/C6.68671. This result treats exactly two physical SMALL labels. Arbitrary-defect completion and the full global strict lexicographic exchange remain open."))), []));
}
