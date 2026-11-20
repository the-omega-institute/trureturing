using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleDiagonal;

internal sealed class GeneralArithmeticDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native diagonal choices and physical gate conversion",
        H("Strict and equality faces with c>=3"),
        Blocks(
            Describe.Lean(DescribeId.Create("helper-general-arithmetic-1"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleDiagonal/GeneralArithmetic.parameterChoice"),
                H("All native diagonal exponents"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a>b>d>c>=3 and a<=c+d, parameterChoice constructs natural masks, capacities, bit inclusion and the twelve seam gates. It uses K=2^(b-d-1), J=2^(a-b-1), g=4KJ=2^(a-d) and m=2^(c-(a-d)); m>=2 is the strict face and m=1 the equality face. The cyclic and equality residue lemmas choose h,r,v, while polynomial corner proofs and affine interpolation establish the rectangle."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("helper-general-arithmetic-2"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleDiagonal/GeneralArithmetic.rectangle_to_twelve"),
                H("Four rectangle slacks imply twelve gates"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This conversion assumes z>=4 and retains the factored positivity and both third-gate slack identities. It applies to fixed-q choices with s=q+r and the stated capacities. no_carry_submask and the dyadic identities convert integer selections to natural masks. Native consumes the diagonal choice and reuses this conversion for other fixed-q regions; the direct small-c2 branch uses a separate conversion."))), DescribeRole.Lemma),
            Paragraph(Text("These existing private declarations are consumed by the strict-saddle endpoint. This mirror documents their stated hypotheses and use; it makes no independent literature-novelty claim, no claim of a four-slot registration for every helper, and no claim to settle unrestricted four-gap J or Circle Conjecture 3.1."))), []));
}
