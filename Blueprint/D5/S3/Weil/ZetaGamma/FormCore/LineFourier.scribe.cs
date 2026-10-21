using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore;

internal sealed class LineFourierDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For F in L1(R) intersect L2(R), angularFourier(F,z)=integral_R exp(-i*z*x)*F(x) dx. Plancherel has factor 1/(2*pi), and the nonnegative Gamma jump energy equals integral_R (Re digamma(1/4+i*z/2)-Re digamma(1/4))*|angularFourier(F,z)|^2 dz divided by 2*pi. Tonelli preserves equality when either side is infinite. For a>0 and any complex L2 profile u on (-a,a], take F=PeriodicEnergyTransport.zeroExtension(2*a,-a,u). Its L2 property is zero_extension_memLp; its L1 property follows from finite interval measure by MemLp.integrable and integrable_indicator_iff. Thus the identity applies to the literal Ioc zero extension, including arbitrary endpoint jumps. No finite Gamma-energy or smoothness assumption is needed for this identity.",
        H("Actual Gamma form core: LineFourier"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gamma-form-core-linefourier-continuous-raw-fourier"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/LineFourier.continuous_raw_fourier"),
                H("continuous raw fourier"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For F in L1(R) intersect L2(R), angularFourier(F,z)=integral_R exp(-i*z*x)*F(x) dx. Plancherel has factor 1/(2*pi), and the nonnegative Gamma jump energy equals integral_R (Re digamma(1/4+i*z/2)-Re digamma(1/4))*|angularFourier(F,z)|^2 dz divided by 2*pi. Tonelli preserves equality when either side is infinite. For a>0 and any complex L2 profile u on (-a,a], take F=PeriodicEnergyTransport.zeroExtension(2*a,-a,u). Its L2 property is zero_extension_memLp; its L1 property follows from finite interval measure by MemLp.integrable and integrable_indicator_iff. Thus the identity applies to the literal Ioc zero extension, including arbitrary endpoint jumps. No finite Gamma-energy or smoothness assumption is needed for this identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-linefourier-squared-mass-eq-elpnorm"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/LineFourier.squared_mass_eq_eLpNorm"),
                H("squared mass eq eLpNorm"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For F in L1(R) intersect L2(R), angularFourier(F,z)=integral_R exp(-i*z*x)*F(x) dx. Plancherel has factor 1/(2*pi), and the nonnegative Gamma jump energy equals integral_R (Re digamma(1/4+i*z/2)-Re digamma(1/4))*|angularFourier(F,z)|^2 dz divided by 2*pi. Tonelli preserves equality when either side is infinite. For a>0 and any complex L2 profile u on (-a,a], take F=PeriodicEnergyTransport.zeroExtension(2*a,-a,u). Its L2 property is zero_extension_memLp; its L1 property follows from finite interval measure by MemLp.integrable and integrable_indicator_iff. Thus the identity applies to the literal Ioc zero extension, including arbitrary endpoint jumps. No finite Gamma-energy or smoothness assumption is needed for this identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-linefourier-angularfourier"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/LineFourier.angularFourier"),
                H("angularFourier"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For F in L1(R) intersect L2(R), angularFourier(F,z)=integral_R exp(-i*z*x)*F(x) dx. Plancherel has factor 1/(2*pi), and the nonnegative Gamma jump energy equals integral_R (Re digamma(1/4+i*z/2)-Re digamma(1/4))*|angularFourier(F,z)|^2 dz divided by 2*pi. Tonelli preserves equality when either side is infinite. For a>0 and any complex L2 profile u on (-a,a], take F=PeriodicEnergyTransport.zeroExtension(2*a,-a,u). Its L2 property is zero_extension_memLp; its L1 property follows from finite interval measure by MemLp.integrable and integrable_indicator_iff. Thus the identity applies to the literal Ioc zero extension, including arbitrary endpoint jumps. No finite Gamma-energy or smoothness assumption is needed for this identity."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-linefourier-angular-extended-plancherel"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/LineFourier.angular_extended_plancherel"),
                H("angular extended plancherel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For F in L1(R) intersect L2(R), angularFourier(F,z)=integral_R exp(-i*z*x)*F(x) dx. Plancherel has factor 1/(2*pi), and the nonnegative Gamma jump energy equals integral_R (Re digamma(1/4+i*z/2)-Re digamma(1/4))*|angularFourier(F,z)|^2 dz divided by 2*pi. Tonelli preserves equality when either side is infinite. For a>0 and any complex L2 profile u on (-a,a], take F=PeriodicEnergyTransport.zeroExtension(2*a,-a,u). Its L2 property is zero_extension_memLp; its L1 property follows from finite interval measure by MemLp.integrable and integrable_indicator_iff. Thus the identity applies to the literal Ioc zero extension, including arbitrary endpoint jumps. No finite Gamma-energy or smoothness assumption is needed for this identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-linefourier-raw-fourier-sub"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/LineFourier.raw_fourier_sub"),
                H("raw fourier sub"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For F in L1(R) intersect L2(R), angularFourier(F,z)=integral_R exp(-i*z*x)*F(x) dx. Plancherel has factor 1/(2*pi), and the nonnegative Gamma jump energy equals integral_R (Re digamma(1/4+i*z/2)-Re digamma(1/4))*|angularFourier(F,z)|^2 dz divided by 2*pi. Tonelli preserves equality when either side is infinite. For a>0 and any complex L2 profile u on (-a,a], take F=PeriodicEnergyTransport.zeroExtension(2*a,-a,u). Its L2 property is zero_extension_memLp; its L1 property follows from finite interval measure by MemLp.integrable and integrable_indicator_iff. Thus the identity applies to the literal Ioc zero extension, including arbitrary endpoint jumps. No finite Gamma-energy or smoothness assumption is needed for this identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-linefourier-linegapmass"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/LineFourier.lineGapMass"),
                H("lineGapMass"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For F in L1(R) intersect L2(R), angularFourier(F,z)=integral_R exp(-i*z*x)*F(x) dx. Plancherel has factor 1/(2*pi), and the nonnegative Gamma jump energy equals integral_R (Re digamma(1/4+i*z/2)-Re digamma(1/4))*|angularFourier(F,z)|^2 dz divided by 2*pi. Tonelli preserves equality when either side is infinite. For a>0 and any complex L2 profile u on (-a,a], take F=PeriodicEnergyTransport.zeroExtension(2*a,-a,u). Its L2 property is zero_extension_memLp; its L1 property follows from finite interval measure by MemLp.integrable and integrable_indicator_iff. Thus the identity applies to the literal Ioc zero extension, including arbitrary endpoint jumps. No finite Gamma-energy or smoothness assumption is needed for this identity."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-linefourier-actualdensity"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/LineFourier.actualDensity"),
                H("actualDensity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For F in L1(R) intersect L2(R), angularFourier(F,z)=integral_R exp(-i*z*x)*F(x) dx. Plancherel has factor 1/(2*pi), and the nonnegative Gamma jump energy equals integral_R (Re digamma(1/4+i*z/2)-Re digamma(1/4))*|angularFourier(F,z)|^2 dz divided by 2*pi. Tonelli preserves equality when either side is infinite. For a>0 and any complex L2 profile u on (-a,a], take F=PeriodicEnergyTransport.zeroExtension(2*a,-a,u). Its L2 property is zero_extension_memLp; its L1 property follows from finite interval measure by MemLp.integrable and integrable_indicator_iff. Thus the identity applies to the literal Ioc zero extension, including arbitrary endpoint jumps. No finite Gamma-energy or smoothness assumption is needed for this identity."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-linefourier-actualincrement"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/LineFourier.actualIncrement"),
                H("actualIncrement"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For F in L1(R) intersect L2(R), angularFourier(F,z)=integral_R exp(-i*z*x)*F(x) dx. Plancherel has factor 1/(2*pi), and the nonnegative Gamma jump energy equals integral_R (Re digamma(1/4+i*z/2)-Re digamma(1/4))*|angularFourier(F,z)|^2 dz divided by 2*pi. Tonelli preserves equality when either side is infinite. For a>0 and any complex L2 profile u on (-a,a], take F=PeriodicEnergyTransport.zeroExtension(2*a,-a,u). Its L2 property is zero_extension_memLp; its L1 property follows from finite interval measure by MemLp.integrable and integrable_indicator_iff. Thus the identity applies to the literal Ioc zero extension, including arbitrary endpoint jumps. No finite Gamma-energy or smoothness assumption is needed for this identity."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-linefourier-cyclicgap"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/LineFourier.cyclicGap"),
                H("cyclicGap"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For F in L1(R) intersect L2(R), angularFourier(F,z)=integral_R exp(-i*z*x)*F(x) dx. Plancherel has factor 1/(2*pi), and the nonnegative Gamma jump energy equals integral_R (Re digamma(1/4+i*z/2)-Re digamma(1/4))*|angularFourier(F,z)|^2 dz divided by 2*pi. Tonelli preserves equality when either side is infinite. For a>0 and any complex L2 profile u on (-a,a], take F=PeriodicEnergyTransport.zeroExtension(2*a,-a,u). Its L2 property is zero_extension_memLp; its L1 property follows from finite interval measure by MemLp.integrable and integrable_indicator_iff. Thus the identity applies to the literal Ioc zero extension, including arbitrary endpoint jumps. No finite Gamma-energy or smoothness assumption is needed for this identity."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-linefourier-actual-line-spectralweight"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/LineFourier.actual_line_spectralWeight"),
                H("actual line spectralWeight"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For F in L1(R) intersect L2(R), angularFourier(F,z)=integral_R exp(-i*z*x)*F(x) dx. Plancherel has factor 1/(2*pi), and the nonnegative Gamma jump energy equals integral_R (Re digamma(1/4+i*z/2)-Re digamma(1/4))*|angularFourier(F,z)|^2 dz divided by 2*pi. Tonelli preserves equality when either side is infinite. For a>0 and any complex L2 profile u on (-a,a], take F=PeriodicEnergyTransport.zeroExtension(2*a,-a,u). Its L2 property is zero_extension_memLp; its L1 property follows from finite interval measure by MemLp.integrable and integrable_indicator_iff. Thus the identity applies to the literal Ioc zero extension, including arbitrary endpoint jumps. No finite Gamma-energy or smoothness assumption is needed for this identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-linefourier-actual-gamma-whole-line-energy-eq-angular-integral"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/LineFourier.actual_gamma_whole_line_energy_eq_angular_integral"),
                H("actual gamma whole line energy eq angular integral"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For F in L1(R) intersect L2(R), angularFourier(F,z)=integral_R exp(-i*z*x)*F(x) dx. Plancherel has factor 1/(2*pi), and the nonnegative Gamma jump energy equals integral_R (Re digamma(1/4+i*z/2)-Re digamma(1/4))*|angularFourier(F,z)|^2 dz divided by 2*pi. Tonelli preserves equality when either side is infinite. For a>0 and any complex L2 profile u on (-a,a], take F=PeriodicEnergyTransport.zeroExtension(2*a,-a,u). Its L2 property is zero_extension_memLp; its L1 property follows from finite interval measure by MemLp.integrable and integrable_indicator_iff. Thus the identity applies to the literal Ioc zero extension, including arbitrary endpoint jumps. No finite Gamma-energy or smoothness assumption is needed for this identity."))),
                DescribeRole.Theorem))));
}
