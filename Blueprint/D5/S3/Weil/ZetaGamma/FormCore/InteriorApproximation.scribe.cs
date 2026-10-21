using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore;

internal sealed class InteriorApproximationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original zero extension is exactly PeriodicEnergyTransport.zeroExtension (2*a) (-a) u. Only MemLp u 2 on Ioc(-a,a) and finite actual energy enter the inward approximation. The singleton endpoint difference from the open window is handled AE, and the whole-line mass equals the original Ioc mass. Choosing a measurable representative preserves both mass and actual energy.",
        H("Actual Gamma form core: InteriorApproximation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gamma-form-core-interiorapproximation-actual-gamma-interior-cutoff-form-approximation"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/InteriorApproximation.actual_gamma_interior_cutoff_form_approximation"),
                H("actual gamma interior cutoff form approximation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original zero extension is exactly PeriodicEnergyTransport.zeroExtension (2*a) (-a) u. Only MemLp u 2 on Ioc(-a,a) and finite actual energy enter the inward approximation. The singleton endpoint difference from the open window is handled AE, and the whole-line mass equals the original Ioc mass. Choosing a measurable representative preserves both mass and actual energy."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-interiorapproximation-actual-ioc-exists-measurable-zero-supported-energy-representative"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/InteriorApproximation.actual_ioc_exists_measurable_zero_supported_energy_representative"),
                H("actual ioc exists measurable zero supported energy representative"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original zero extension is exactly PeriodicEnergyTransport.zeroExtension (2*a) (-a) u. Only MemLp u 2 on Ioc(-a,a) and finite actual energy enter the inward approximation. The singleton endpoint difference from the open window is handled AE, and the whole-line mass equals the original Ioc mass. Choosing a measurable representative preserves both mass and actual energy."))),
                DescribeRole.Theorem))));
}
