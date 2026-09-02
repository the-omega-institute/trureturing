using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Pick;

internal sealed class LocalizedStieltjesToWeilQuadraticInterfaceDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/Pick/LocalizedStieltjesToWeilQuadraticInterface.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An explicit exact-readout interface isolates the analytic obligation needed to turn "
            + "an active localized Stieltjes orbit into a negative Weil quadratic test.",
        H("Localized Stieltjes-to-Weil Quadratic Interface"),
        Blocks(
            DefinitionNode(),
            Describe.Lean(
                DescribeId.Create("active-orbit-produces-negative-weil-value"),
                DeclarationHandle.Create(
                    Prefix + "active_orbit_gives_negative_weil_value"),
                H("An active orbit produces a negative Weil value"),
                StatementSource.FromAuthor(ActiveTransportFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The proof substitutes the exact readout identity and applies the positive-"
                        + "mass barcode sign theorem. All analytic realization work is confined "
                        + "to the transport structure."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("an-active-orbit-produces-some-negative-weil-test"),
                DeclarationHandle.Create(
                    Prefix + "exists_negative_weil_test_of_active_orbit"),
                H("An active orbit produces some negative Weil test"),
                StatementSource.FromAuthor(ExistenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This packages the selected orbit's realized test as an existential negative "
                        + "direction in the target quadratic domain."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nonnegative-weil-form-rules-out-active-orbits"),
                DeclarationHandle.Create(
                    Prefix + "no_active_orbit_of_nonnegative_weil_form"),
                H("A nonnegative Weil form rules out active orbits"),
                StatementSource.FromAuthor(NonnegativeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under an exact positive-mass transport, target nonnegativity contradicts "
                        + "the negative value forced by any active orbit."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Weil/Pick/ObserverSignedSupportBarcode")),
        ]));

    private static DocumentBlock.Describe DefinitionNode() =>
        Describe.Lean(
            DescribeId.Create("exact-localized-stieltjes-weil-transport"),
            DeclarationHandle.Create(
                Prefix + "ExactLocalizedStieltjesWeilTransport"),
            H("Exact localized Stieltjes-Weil transport"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "The structure contains an orbit-to-test realization, a real target quadratic "
                    + "functional, and an exact equality with each localized atomic weight."))),
            DescribeRole.Definition);

    private static Formula ActiveTransportFormula() =>
        F.Disp(F.Id("activePositiveMassOrbitGivesNegativeWeilValue"));

    private static Formula ExistenceFormula() =>
        F.Disp(F.Id("activeOrbitGivesSomeNegativeWeilTest"));

    private static Formula NonnegativeFormula() =>
        F.Disp(F.Id("nonnegativeWeilFormRulesOutActiveOrbits"));
}
