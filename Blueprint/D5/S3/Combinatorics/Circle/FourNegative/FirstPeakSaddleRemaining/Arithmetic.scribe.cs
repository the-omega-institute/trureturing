using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleRemaining;

internal sealed class ArithmeticDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer selections and native mask conversion",
        H("Shared arithmetic for high, half and quarter regions"),
        Blocks(
            Describe.Lean(DescribeId.Create("helper-arithmetic-1"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleRemaining/Arithmetic.scaled_to_rectangle"),
                H("Recover the four unscaled slacks"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("rectangle lists E+C,A-1-E,H-A+qD,L-C-H in physical argument order t,z,x,y,g,q,r,h,v. scaled_margin avoids division by the auxiliary scale. Positive scale and z+1 together with ps-js=2*scale*(z+1)*v identify each scaled entry with the same positive multiple of its rectangle entry."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("helper-arithmetic-2"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleRemaining/Arithmetic.native_of_selection"),
                H("Convert an integer choice to natural masks"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("ArithmeticSelection supplies r,h,v, their capacities and all four rectangle margins with x=4KJt,y=2Kt,g=4KJ,q=2KJt-4KJ. native_of_selection uses K=2^(b-d-1), J=2^(a-b-1), casts nonnegative selections to naturals and sets s=2^(a-d)*(2^(d-1)-1)+r. NativeChoice retains the anchor, grain bound, bit inclusion and rectangle evidence. Each consuming region must supply its own selection; this conversion does not assume or assert arbitrary feasibility."))), DescribeRole.Definition),
            Paragraph(Text("These existing private declarations are consumed by the strict-saddle endpoint. This mirror documents their stated hypotheses and use; it makes no independent literature-novelty claim, no claim of a four-slot registration for every helper, and no claim to settle unrestricted four-gap J or Circle Conjecture 3.1."))), []));
}
