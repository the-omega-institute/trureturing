using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic;

internal sealed class ActualUnattainedWeightedWindowsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two signs of the actual weighted psi tail in late windows",
        H("Two signs of the actual weighted psi tail in late windows"),
        Blocks(Describe.Lean(
            DescribeId.Create("eventually-actual-weighted-psi-tail-two-signs"),
            DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/ActualUnattainedWeightedWindows.eventually_actual_weighted_psi_tail_two_signs"),
            H("Two signs of the actual weighted psi tail in late windows"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("When the zero abscissa is unattained, arbitrarily short probability corrections preserve a high-frequency dominant conjugate pair. Each sufficiently late logarithmic window of fixed positive width contains both raw signs at the predicted power scale divided by the logarithmic variable."))),
            DescribeRole.Theorem))));
}
