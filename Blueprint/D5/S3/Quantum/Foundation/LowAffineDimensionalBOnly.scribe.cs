using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class LowAffineDimensionalBOnlyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original whole-base ball branch of VII98.7 supplies an ambient proper antipodal effect.",
        H("Whole-base ball branch of VII98.7"),
        Blocks(
            Paragraph(Text("For the original finite-dimensional closed pointed generating cone and its original strictly positive unit, an entire pair ball equal to the whole normalized base yields a genuine linear proper effect separating every unit antipodal chart pair.")),
            Describe.Lean(DescribeId.Create("ball-chart-antipodal-effect"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/LowAffineDimensionalBOnly.ball_chart_antipodal_effect"),
                H("A whole-base chart gives a proper antipodal effect"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The chart coordinate functional is extended from the chart direction to the entire original carrier. Properness is checked on every cone element by normalization into the whole base."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("all-antipodes-of-full-pair-balls"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/LowAffineDimensionalBOnly.allAntipodes_of_full_pair_balls"),
                H("Consumer: the original allAntipodes predicate"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("When every distinct pure pair has a chart whose pair base is the whole base, the preceding effect supplies allAntipodes on the original carrier."))), DescribeRole.Theorem),
            Paragraph(Text("The segment-face and positive-dimensional-facet branches of the complete VII98.7 theorem require additional geometric arguments.")))));
}
