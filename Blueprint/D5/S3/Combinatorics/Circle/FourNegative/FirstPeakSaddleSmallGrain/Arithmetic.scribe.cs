using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleSmallGrain;

internal sealed class ArithmeticDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Direct masks for the low-a c=2 branch",
        H("Three dyadic ratios and exact fixed exceptions"),
        Blocks(
            Describe.Lean(DescribeId.Create("helper-arithmetic-1"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleSmallGrain/Arithmetic.select_chart"),
                H("Select direct masks and all nineteen margins"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a>b>d>=3 and a<=d+3, the ratio pairs (K,J) are exactly (1,1),(1,2),(2,1). Shared ModTen.phase_cover chooses the four unbounded phases or d=3. The three fixed t=8 checks remain inline in their respective selector branches, with 19 margins each. All-one-mask and even-s cases preserve the actual submask; no fixed-q, grain-bound or reserve-anchor condition is imposed."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("helper-arithmetic-2"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleSmallGrain/Arithmetic.arithmetic_choice_exists"),
                H("Existence in the complete small-c2 branch"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("choice_of_margins converts the nineteen exact margins to natural s,r,h,v with capacities, inclusion of r-1 in s-1 and the physical seam inequalities. The twelve phase charts in Certificates plus three inline fixed checks give 15 charts and 285 margins. Native converts the first twelve entries directly to JointChoice. This result covers a<=d+3; QuarterStep supplies the complementary c=2 branch."))), DescribeRole.Lemma),
            Paragraph(Text("These existing private declarations are consumed by the strict-saddle endpoint. This mirror documents their stated hypotheses and use; it makes no independent literature-novelty claim, no claim of a four-slot registration for every helper, and no claim to settle unrestricted four-gap J or Circle Conjecture 3.1."))), []));
}
