using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddle;

internal sealed class ModTenDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact dyadic phases modulo ten",
        H("Shared phases for the two c=2 constructions"),
        Blocks(
            Describe.Lean(DescribeId.Create("helper-mod-ten-1"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddle/ModTen.phase_cover"),
                H("Dyadic phase cover"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural d>=3, either d=3 or 2^d is 16, 32, 64 or 128 plus ten times a natural number. pow2mod10 proves the four-period residue cycle by induction; the phase proof also establishes the lower bound needed for natural subtraction. The small-c2 selector consumes these alternatives, including its separate d=3 case."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("helper-mod-ten-2"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddle/ModTen.quarter_phase_cover"),
                H("Quarter-step phase cover"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The quarter-step version absorbs the 128 phase into 8+10*T, giving the four bases 8,16,32,64. QuarterStep.quarter_arithmetic consumes this cover. These are residue classes for unbounded exponents, not a finite search over exponent values."))), DescribeRole.Lemma),
            Paragraph(Text("These existing private declarations are consumed by the strict-saddle endpoint. This mirror documents their stated hypotheses and use; it makes no independent literature-novelty claim, no claim of a four-slot registration for every helper, and no claim to settle unrestricted four-gap J or Circle Conjecture 3.1."))), []));
}
