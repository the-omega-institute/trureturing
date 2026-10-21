using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore;

internal sealed class CutoffConvergenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual smooth-mask commutator limit and the exterior budget dominate the outer integral, giving cutoff error energy tending to zero for measurable whole-line L2 inputs supported in the open window with finite actual energy. AE congruence then selects a measurable exactly zero-supported representative without adding pointwise regularity to the original source input.",
        H("Actual Gamma form core: CutoffConvergence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gamma-form-core-cutoffconvergence-actual-gamma-cutoff-error-energy-tendsto-zero"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/CutoffConvergence.actual_gamma_cutoff_error_energy_tendsto_zero"),
                H("actual gamma cutoff error energy tendsto zero"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual smooth-mask commutator limit and the exterior budget dominate the outer integral, giving cutoff error energy tending to zero for measurable whole-line L2 inputs supported in the open window with finite actual energy. AE congruence then selects a measurable exactly zero-supported representative without adding pointwise regularity to the original source input."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-cutoffconvergence-directionalenergy-congr-ae"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/CutoffConvergence.directionalEnergy_congr_ae"),
                H("directionalEnergy congr ae"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual smooth-mask commutator limit and the exterior budget dominate the outer integral, giving cutoff error energy tending to zero for measurable whole-line L2 inputs supported in the open window with finite actual energy. AE congruence then selects a measurable exactly zero-supported representative without adding pointwise regularity to the original source input."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-cutoffconvergence-exists-measurable-zero-supported-energy-representative"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/CutoffConvergence.exists_measurable_zero_supported_energy_representative"),
                H("exists measurable zero supported energy representative"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual smooth-mask commutator limit and the exterior budget dominate the outer integral, giving cutoff error energy tending to zero for measurable whole-line L2 inputs supported in the open window with finite actual energy. AE congruence then selects a measurable exactly zero-supported representative without adding pointwise regularity to the original source input."))),
                DescribeRole.Theorem))));
}
