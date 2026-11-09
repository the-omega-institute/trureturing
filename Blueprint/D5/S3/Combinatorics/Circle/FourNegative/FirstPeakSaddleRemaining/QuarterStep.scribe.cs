using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleRemaining;

internal sealed class QuarterStepDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Quarter-step choices for c=2",
        H("The branch a>=d+4 and b<=d+2"),
        Blocks(
            Describe.Lean(DescribeId.Create("helper-quarter-step-1"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleRemaining/QuarterStep.quarter_arithmetic"),
                H("Eight unbounded phase charts"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For d>=3,f>=1 and either (K,F)=(1,2) or (2,1), quarter_arithmetic constructs ArithmeticSelection with z=4 and J=2Ff. The shared quarter_phase_cover selects t=8,16,32,64 modulo ten. Eight charts prove nine margins each, including capacities, for all nonnegative phase and scale parameters. quarter_of_margins turns these 72 margins into the integer record."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("helper-quarter-step-2"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleRemaining/QuarterStep.quarter_step_choice_exists"),
                H("Native quarter-step masks"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a>b>d>=3, b<=d+2 and a>=d+4, dyadic ratios yield the two (K,F) cases and f=2^(a-d-4). The native conversion supplies the anchored submask and rectangle margins. Native consumes this branch at c=2; the separate low-a small-c2 construction is not replaced or given a fixed-q assumption."))), DescribeRole.Lemma),
            Paragraph(Text("These existing private declarations are consumed by the strict-saddle endpoint. This mirror documents their stated hypotheses and use; it makes no independent literature-novelty claim, no claim of a four-slot registration for every helper, and no claim to settle unrestricted four-gap J or Circle Conjecture 3.1."))), []));
}
