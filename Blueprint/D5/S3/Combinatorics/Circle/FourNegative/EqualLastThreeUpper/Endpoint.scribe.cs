using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.EqualLastThreeUpper;
internal sealed class EndpointDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An actual physical joint-prefix family for all a>=s>=2",
        H("Equal last three gaps with an explicit literal cut"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-source-equal-last-three-upper-joint-lift"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/EqualLastThreeUpper/Endpoint.actualSource_equal_last_three_upper_joint_lift"),
                H("Every s>=2 and a>=s"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let k=a+3s and A=1+2^a+2^(a+s)+2^(a+2s). For every s>=2 and a>=s there is a physical permutation sigma for OriginalOrder(k,A) such that the same sigma with the fresh label k inserted at j is an OriginalOrder(k+1,2A). The numeric cut is j=s-1 if a=s, and j=3s if a>s. The statement also fixes sigma's entire natural-label word: native range(k) in the equality case, and range'(a+2s-1,s+1) ++ range(3s-1) ++ range'(3s,a-s-1) ++ [3s-1] in the strict case. Here range' uses a start and a length. Each OriginalOrder includes the full physical inventory, exact total zero, and the half-modulus strip for every natural take-prefix.")),
                    Paragraph(Text("The strict construction splits the X-positive chain into its high interval of length s and its low interval of length a-s-1. It puts the high part and X- first, then native U and native V, and puts native W and the low X part before W-. The ear has actual value A and is immediately before V-. The recurrences at offsets 0,s,2s,3s identify the actual centered values; exact geometric interval masses and doubled polynomial inequalities give both rows' seams and peak bounds. Positive-bag monotonicity controls every intervening prefix. At a=s, native physical order and an ear before U- give the equality construction. Equal numerical values retain all their distinct physical labels.")),
                    Paragraph(Text("Attribution: Pro task b882f14d-1d25-4689-b46f-9960312490d7 supplied the construction for a>=2s. The caller extended its inequalities to a>s using only h=2^(a-s)>=2 and supplied the separate a=s construction. The finite centered-source controls accompanying that ordinary proof are diagnostic examples and are not premises of this theorem.")),
                    Paragraph(Text("This is a subfamily of the actual four-gap joint-prefix problem associated with Circle Conjecture 3.1 in Damasdi, Frankl, Pach and Palvolgyi, Monochromatic configurations on a circle, arXiv:2504.10687v2. The region 2<=a<s and unrestricted physical four-gap J remain open. No gap rotation or reversal covariance, primitive orbit, residue distinctness, allocation certificate, or feasibility assumption is required. No external novelty claim is made."))),
                DescribeRole.Theorem)), []));
}
