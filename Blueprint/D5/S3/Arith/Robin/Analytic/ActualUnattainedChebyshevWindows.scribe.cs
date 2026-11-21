using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic;

internal sealed class ActualUnattainedChebyshevWindowsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both signs in each sufficiently late Chebyshev log window",
        H("Both signs in each sufficiently late Chebyshev log window"),
        Blocks(Describe.Lean(
            DescribeId.Create("eventually-actual-chebyshev-tail-two-signs"),
            DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/ActualUnattainedChebyshevWindows.eventually_actual_chebyshev_tail_two_signs"),
            H("Both signs in each sufficiently late Chebyshev log window"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Under unattainment, every sufficiently late logarithmic window of any fixed positive width contains a positive and a negative value of the actual complete Chebyshev tail. Each excursion is bounded below in magnitude at an exponent strictly to the right of the prescribed strip."))),
            DescribeRole.Theorem))));
}
