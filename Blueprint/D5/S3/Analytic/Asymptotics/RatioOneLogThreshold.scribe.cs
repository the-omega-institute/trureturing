using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Asymptotics;

internal sealed class RatioOneLogThresholdDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer enumerations with adjacent ratios tending to one",
        H("Integer enumerations with adjacent ratios tending to one"),
        Blocks(Describe.Lean(
            DescribeId.Create("strict-mono-ratio-tends-to-one-from-log-windows"),
            DeclarationHandle.Create("D5/S3/Analytic/Asymptotics/RatioOneLogThreshold.exists_strictMono_ratio_tendsto_one_of_log_windows"),
            H("Integer enumerations with adjacent ratios tending to one"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("If positive integers satisfying a predicate meet every sufficiently late logarithmic window of each fixed positive width, their increasing enumeration has adjacent ratios tending to one."))),
            DescribeRole.Theorem))));
}
