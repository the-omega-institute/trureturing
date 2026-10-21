using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore;

internal sealed class ExteriorBudgetDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The jump measure is the positive-half-line Lebesgue measure withDensity ofReal(rho). For an interior point its ENNReal exit potential equals ofReal of the two actual Gamma tails at a-y and a+y. Finite actual directional energy and zero support outside Ioo(-a,a) control the exterior-weighted L2 mass. The proof does not assume an independent boundary or endpoint budget.",
        H("Actual Gamma form core: ExteriorBudget"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gamma-form-core-exteriorbudget-actualgammaexitmeasure"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/ExteriorBudget.actualGammaExitMeasure"),
                H("actualGammaExitMeasure"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The jump measure is the positive-half-line Lebesgue measure withDensity ofReal(rho). For an interior point its ENNReal exit potential equals ofReal of the two actual Gamma tails at a-y and a+y. Finite actual directional energy and zero support outside Ioo(-a,a) control the exterior-weighted L2 mass. The proof does not assume an independent boundary or endpoint budget."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-exteriorbudget-actual-gamma-exteriorpotential-eq-ofreal"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/ExteriorBudget.actual_gamma_exteriorPotential_eq_ofReal"),
                H("actual gamma exteriorPotential eq ofReal"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The jump measure is the positive-half-line Lebesgue measure withDensity ofReal(rho). For an interior point its ENNReal exit potential equals ofReal of the two actual Gamma tails at a-y and a+y. Finite actual directional energy and zero support outside Ioo(-a,a) control the exterior-weighted L2 mass. The proof does not assume an independent boundary or endpoint budget."))),
                DescribeRole.Theorem))));
}
