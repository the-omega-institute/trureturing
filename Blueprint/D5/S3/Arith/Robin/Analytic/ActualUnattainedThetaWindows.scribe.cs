using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic;

internal sealed class ActualUnattainedThetaWindowsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two signs of the actual weighted Robin theta tail in late windows",
        H("Two signs of the actual weighted Robin theta tail in late windows"),
        Blocks(Describe.Lean(
            DescribeId.Create("eventually-actual-weighted-theta-tail-two-signs"),
            DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/ActualUnattainedThetaWindows.eventually_actual_weighted_theta_tail_two_signs"),
            H("Two signs of the actual weighted Robin theta tail in late windows"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Prime powers contribute only at the square-root scale. Under unattainment the actual Robin theta tail takes both signs at a strictly larger power scale in each sufficiently late fixed logarithmic window."))),
            DescribeRole.Theorem))));
}
