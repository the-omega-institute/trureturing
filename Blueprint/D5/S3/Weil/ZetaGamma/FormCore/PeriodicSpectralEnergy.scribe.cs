using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore;

internal sealed class PeriodicSpectralEnergyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For d>0 and every original Ioc interval MemLp 2 input, including infinite full energy, the periodic actual-Gamma energy equals the ENNReal coefficient sum. The coefficient is sqrt(d) times Mathlib fourierCoeff with probability Haar measure, so its square has physical Lebesgue normalization. Parseval and nonnegative Tonelli give the phase-gap sum; the canonical owner Levy integral evaluates the weight to Re digamma(1/4+i*omega/2)-Re digamma(1/4).",
        H("Actual Gamma form core: PeriodicSpectralEnergy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gamma-form-core-periodicspectralenergy-phasegap"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/PeriodicSpectralEnergy.phaseGap"),
                H("phaseGap"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For d>0 and every original Ioc interval MemLp 2 input, including infinite full energy, the periodic actual-Gamma energy equals the ENNReal coefficient sum. The coefficient is sqrt(d) times Mathlib fourierCoeff with probability Haar measure, so its square has physical Lebesgue normalization. Parseval and nonnegative Tonelli give the phase-gap sum; the canonical owner Levy integral evaluates the weight to Re digamma(1/4+i*omega/2)-Re digamma(1/4)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-periodicspectralenergy-angularfrequency"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/PeriodicSpectralEnergy.angularFrequency"),
                H("angularFrequency"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For d>0 and every original Ioc interval MemLp 2 input, including infinite full energy, the periodic actual-Gamma energy equals the ENNReal coefficient sum. The coefficient is sqrt(d) times Mathlib fourierCoeff with probability Haar measure, so its square has physical Lebesgue normalization. Parseval and nonnegative Tonelli give the phase-gap sum; the canonical owner Levy integral evaluates the weight to Re digamma(1/4+i*omega/2)-Re digamma(1/4)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-periodicspectralenergy-physicalcoeff"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/PeriodicSpectralEnergy.physicalCoeff"),
                H("physicalCoeff"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For d>0 and every original Ioc interval MemLp 2 input, including infinite full energy, the periodic actual-Gamma energy equals the ENNReal coefficient sum. The coefficient is sqrt(d) times Mathlib fourierCoeff with probability Haar measure, so its square has physical Lebesgue normalization. Parseval and nonnegative Tonelli give the phase-gap sum; the canonical owner Levy integral evaluates the weight to Re digamma(1/4+i*omega/2)-Re digamma(1/4)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-periodicspectralenergy-windowgapmass"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/PeriodicSpectralEnergy.windowGapMass"),
                H("windowGapMass"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For d>0 and every original Ioc interval MemLp 2 input, including infinite full energy, the periodic actual-Gamma energy equals the ENNReal coefficient sum. The coefficient is sqrt(d) times Mathlib fourierCoeff with probability Haar measure, so its square has physical Lebesgue normalization. Parseval and nonnegative Tonelli give the phase-gap sum; the canonical owner Levy integral evaluates the weight to Re digamma(1/4+i*omega/2)-Re digamma(1/4)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-periodicspectralenergy-extended-window-energy-eq-tsum"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/PeriodicSpectralEnergy.extended_window_energy_eq_tsum"),
                H("extended window energy eq tsum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For d>0 and every original Ioc interval MemLp 2 input, including infinite full energy, the periodic actual-Gamma energy equals the ENNReal coefficient sum. The coefficient is sqrt(d) times Mathlib fourierCoeff with probability Haar measure, so its square has physical Lebesgue normalization. Parseval and nonnegative Tonelli give the phase-gap sum; the canonical owner Levy integral evaluates the weight to Re digamma(1/4+i*omega/2)-Re digamma(1/4)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-periodicspectralenergy-gammadensity"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/PeriodicSpectralEnergy.gammaDensity"),
                H("gammaDensity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For d>0 and every original Ioc interval MemLp 2 input, including infinite full energy, the periodic actual-Gamma energy equals the ENNReal coefficient sum. The coefficient is sqrt(d) times Mathlib fourierCoeff with probability Haar measure, so its square has physical Lebesgue normalization. Parseval and nonnegative Tonelli give the phase-gap sum; the canonical owner Levy integral evaluates the weight to Re digamma(1/4+i*omega/2)-Re digamma(1/4)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-periodicspectralenergy-gammaincrement"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/PeriodicSpectralEnergy.gammaIncrement"),
                H("gammaIncrement"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For d>0 and every original Ioc interval MemLp 2 input, including infinite full energy, the periodic actual-Gamma energy equals the ENNReal coefficient sum. The coefficient is sqrt(d) times Mathlib fourierCoeff with probability Haar measure, so its square has physical Lebesgue normalization. Parseval and nonnegative Tonelli give the phase-gap sum; the canonical owner Levy integral evaluates the weight to Re digamma(1/4+i*omega/2)-Re digamma(1/4)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-periodicspectralenergy-actual-gamma-spectralweight"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/PeriodicSpectralEnergy.actual_gamma_spectralWeight"),
                H("actual gamma spectralWeight"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For d>0 and every original Ioc interval MemLp 2 input, including infinite full energy, the periodic actual-Gamma energy equals the ENNReal coefficient sum. The coefficient is sqrt(d) times Mathlib fourierCoeff with probability Haar measure, so its square has physical Lebesgue normalization. Parseval and nonnegative Tonelli give the phase-gap sum; the canonical owner Levy integral evaluates the weight to Re digamma(1/4+i*omega/2)-Re digamma(1/4)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-periodicspectralenergy-actual-gamma-periodic-energy-eq-tsum"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/PeriodicSpectralEnergy.actual_gamma_periodic_energy_eq_tsum"),
                H("actual gamma periodic energy eq tsum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For d>0 and every original Ioc interval MemLp 2 input, including infinite full energy, the periodic actual-Gamma energy equals the ENNReal coefficient sum. The coefficient is sqrt(d) times Mathlib fourierCoeff with probability Haar measure, so its square has physical Lebesgue normalization. Parseval and nonnegative Tonelli give the phase-gap sum; the canonical owner Levy integral evaluates the weight to Re digamma(1/4+i*omega/2)-Re digamma(1/4)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gammaincrement-nonneg"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/PeriodicSpectralEnergy.gammaIncrement_nonneg"),
                H("Nonnegative digamma increment"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real angular frequency z, Re digamma(1/4+i*z/2)-Re digamma(1/4) is nonnegative. Its nonnegative Levy integral proves this real inequality before conversion to an extended nonnegative number."))),
                DescribeRole.Theorem))));
}
