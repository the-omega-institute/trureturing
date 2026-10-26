using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore;

internal sealed class LineFourierDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For arbitrary complex F in L1(R) intersect L2(R), angularFourier(F,z) is the raw Fourier transform at z/(2*pi), with kernel exp(-i*z*x). Plancherel and the actual Gamma jump-energy identity use exactly 1/(2*pi). The energy identity is in ENNReal and permits infinite Gamma energy. The multiplier is Re digamma(1/4+i*z/2)-Re digamma(1/4), not a surrogate weight. For an Ioc L2 input, the literal PeriodicEnergyTransport.zeroExtension is L2 by zero_extension_memLp and L1 by finite interval measure and integrable_indicator_iff; this explains the application without adding a new zero-extension theorem here. No parity or reality restriction is imposed.",
        H("Actual Gamma form core: LineFourier"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gamma-form-core-linefourier-continuous-raw-fourier"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/LineFourier.continuous_raw_fourier"),
                H("continuous raw fourier"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any integrable complex function on the real line, its raw Mathlib Fourier transform is continuous. Continuity follows from VectorFourier.fourierIntegral_continuous and supplies the measurability needed by the L1/L2 bridge and energy Tonelli proof."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-linefourier-squared-mass-eq-elpnorm"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/LineFourier.squared_mass_eq_eLpNorm"),
                H("squared mass eq eLpNorm"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any AEStronglyMeasurable complex function, its extended squared mass is the square of its extended L2 seminorm. No MemLp or finite-mass hypothesis is added. The proof uses eLpNorm_nnreal_pow_eq_lintegral to relate the spatial and Fourier squared masses in the Plancherel bridge."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-linefourier-angularfourier"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/LineFourier.angularFourier"),
                H("angularFourier"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The angular Fourier transform is the raw Fourier transform evaluated at z/(2*pi). The existing private integral calculation identifies the kernel exp(-i*z*x), fixing the sign and angular normalization for arbitrary complex inputs."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-linefourier-angular-extended-plancherel"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/LineFourier.angular_extended_plancherel"),
                H("angular extended plancherel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every complex L1 and L2 input, extended spatial squared mass equals 1/(2*pi) times extended angular Fourier squared mass. The proof identifies the raw transform with the L2 transform almost everywhere and changes frequency variables by exactly 2*pi."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-linefourier-raw-fourier-sub"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/LineFourier.raw_fourier_sub"),
                H("raw fourier sub"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The raw transform of f-g is the pointwise difference of transforms when f and g are integrable complex functions. The integral_sub identity is used in the translation-gap calculation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-linefourier-linegapmass"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/LineFourier.lineGapMass"),
                H("lineGapMass"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The ordinary squared translation-gap mass is the whole-line integral of norm(f(x)-f(x-s)) squared. In the energy proof each such integral is justified by the L2 hypothesis; finiteness of the subsequent Gamma-energy integral is not assumed."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-linefourier-actualdensity"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/LineFourier.actualDensity"),
                H("actualDensity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The density is exp(-s/2)/(1-exp(-2*s)), selected from ArchimedeanJumpDecomposition.archimedeanJumpDensity. Its nonnegativity on positive rates, Levy kernel integrability and digamma evaluation supply the spectral weight identity."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-linefourier-actualincrement"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/LineFourier.actualIncrement"),
                H("actualIncrement"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual increment at real z is Re digamma(1/4+i*z/2)-Re digamma(1/4), with the displayed real-to-complex coercion and no clipping inside this real-valued definition."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-linefourier-cyclicgap"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/LineFourier.cyclicGap"),
                H("cyclicGap"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The line phase-gap multiplier is 2*(1-cos((2*pi*xi)*s)). It retains both signs of xi and is used in the extended nonnegative frequency integral."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-linefourier-actual-line-spectralweight"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/LineFourier.actual_line_spectralWeight"),
                H("actual line spectralWeight"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real raw frequency xi, the nonnegative density-weighted phase-gap lintegral equals ofReal(actualIncrement(2*pi*xi)). Levy kernel integrability and nonnegativity convert the integral to a lintegral, and ArchimedeanJumpDecomposition.levy_integral_eq_digamma_increment evaluates it."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-linefourier-actual-gamma-whole-line-energy-eq-angular-integral"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/LineFourier.actual_gamma_whole_line_energy_eq_angular_integral"),
                H("actual gamma whole line energy eq angular integral"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every complex whole-line L1 and L2 input, the density-weighted translation-gap lintegral equals 1/(2*pi) times the actual-digamma-weighted angular Fourier squared-mass lintegral. Tonelli is applied before any finiteness restriction, so the ENNReal identity retains infinite Gamma energy."))),
                DescribeRole.Theorem))));
}
