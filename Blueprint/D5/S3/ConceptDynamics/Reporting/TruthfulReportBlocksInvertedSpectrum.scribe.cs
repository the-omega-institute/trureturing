using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Reporting;

internal sealed class TruthfulReportBlocksInvertedSpectrumDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Reporting/TruthfulReportBlocksInvertedSpectrum.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact public recovery forces phenomenal agreement; an inverted pair refutes it.",
        H("Truthful Reporting Blocks an Inverted Spectrum"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("truthful-public-report-forces-phenomenal-agreement"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "truthful_public_report_forces_phenomenal_agreement"),
                H("Truthful public reporting forces phenomenal agreement"),
                StatementSource.FromAuthor(TruthfulReportAgreementFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "TruthfulPublicReport(p, q) requires a total recovery map from every "
                            + "public value to a phenomenal value, with p equal to that map "
                            + "after q. Thus the phenomenal readout is determined entirely by "
                            + "the public readout.")),
                    Paragraph(Text(
                        "Consequently, any two states in the same public fiber must have the "
                            + "same phenomenal value. The conclusion concerns every pair of "
                            + "states, not only values in a chosen or observed part of the "
                            + "public image."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula ImpliesFormula(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula TypeUniverse() => F.Id("Type");

    private static Formula TruthfulReportAgreementFormula()
    {
        Formula stateType = F.Id("State");
        Formula phenomenalType = F.Id("Phenomenal");
        Formula publicType = F.Id("Public");
        Formula phenomenal = F.Id("p");
        Formula publicReadout = F.Id("q");
        Formula left = F.Id("x");
        Formula right = F.Id("y");
        Formula samePublicValue = Equal(
            Apply(publicReadout, left),
            Apply(publicReadout, right));
        Formula samePhenomenalValue = Equal(
            Apply(phenomenal, left),
            Apply(phenomenal, right));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("State", TypeUniverse()),
                Bound("Phenomenal", TypeUniverse()),
                Bound("Public", TypeUniverse()),
                Bound("p", Arrow(stateType, phenomenalType)),
                Bound("q", Arrow(stateType, publicType)),
                Bound("x", stateType),
                Bound("y", stateType),
            ],
            ImpliesFormula(
                Call("TruthfulPublicReport", phenomenal, publicReadout),
                ImpliesFormula(samePublicValue, samePhenomenalValue))));
    }
}
