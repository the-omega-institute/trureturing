using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma;

internal sealed class PeriodicEnergyTransportDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original half-open interval L2 data transport through the actual circle, correlations and noncentral image lattice.",
        H("Periodic energy transport"),
        Blocks(
            Paragraph(Text(
                "For d,t real put I=(t,t+d], windowMeasure(d,t)=Lebesgue measure restricted to I, "
                + "zeroExtension=1_I*u, periodicExtension(x)=AddCircle.liftIoc(d,t,u)(x mod d), "
                + "and windowEnergy=integral_I |u|^2. The two translation energies integrate "
                + "|z(x)-z(x-s)|^2 over the real line and |u(x)-v(x-s)|^2 over I, respectively. "
                + "The correlations use conjugate(z(x))*z(x-s) and conjugate(u(x))*v(x-s).")),
            Paragraph(Text(
                "For an arbitrary real weight w, weightedDifferenceCorrelation(x,s) is "
                + "w(s)*conjugate(u(x))*(v(x-s)-z(x-s)). The image kernel is the sum of "
                + "w(x-y+m*d) over all nonzero integers m. Its reflection and Fubini helpers, "
                + "the unique-copy norm and absolute-sum identities, and the L2 difference "
                + "expansions are consumed by the actual periodic Gamma comparison.")),
            Describe.Lean(
                DescribeId.Create("periodic-transport-periodic-minus-zero-norm-le"),
                DeclarationHandle.Create(Owner + "periodic_minus_zero_norm_le"),
                H("periodic minus zero norm le"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every positive period d, base point t, complex function u and real z, removing the central zero-extension copy has norm at most the actual periodic-extension value. No measurability or endpoint-value hypothesis is used."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("periodic-transport-copy-reflection-measure-preserving"),
                DeclarationHandle.Create(Owner + "copyReflection_measurePreserving"),
                H("copyReflection measurePreserving"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary real d and t and integer m, the involution (x,y) maps to (x,x+m*d-y) and preserves windowMeasure(d,t) times Lebesgue measure. It is the same reflection used for every lattice copy and for the central copy."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("periodic-transport-window-measure-prod-window-measure"),
                DeclarationHandle.Create(Owner + "windowMeasure_prod_windowMeasure"),
                H("windowMeasure prod windowMeasure"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary d and t, the product of the two window measures equals windowMeasure(d,t) times Lebesgue measure restricted to R times (t,t+d]. This pays the second physical-window restriction exactly."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("periodic-transport-weighted-lattice-image-integrable-and-identity"),
                DeclarationHandle.Create(Owner + "weightedLattice_image_integrable_and_identity"),
                H("weightedLattice image integrable and identity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive d, arbitrary t, a real weight w and a complex function u, assume the weighted difference correlation is integrable on the physical window times the real shift line. Then the full noncentral image pairing is integrable on the window square and its integral equals that actual weighted difference-correlation integral. The coefficient of this Hermitian image pairing is one. The proof uses the unique half-open copy, absolute Tonelli, the same measure-preserving reflection on each copy, and absolutely summable Fubini. Its weightedImageKernel sums every nonzero integer image; it omits only the zero image."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("periodic-transport-periodic-shift-mem-lp"),
                DeclarationHandle.Create(Owner + "periodic_shift_memLp"),
                H("periodic shift memLp"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every positive period d and arbitrary base point t, interval MemLp(u,2) implies interval MemLp of x mapping to the actual periodic extension at x-s, for every real displacement s. Haar translation is transported by AddCircle.liftIoc; the original representative needs no global measurability."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("periodic-transport-periodic-correlation-integrable-le"),
                DeclarationHandle.Create(Owner + "periodic_correlation_integrable_le"),
                H("periodic correlation integrable le"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive d and interval MemLp(u,2), the product |u(x)| times |periodicExtension(d,t,u,x-s)| is integrable on the original window and its integral is at most windowEnergy(d,t,u), for every real s. The measure has physical mass d and is not normalized to one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("periodic-transport-periodic-shift-joint-aestrongly-measurable"),
                DeclarationHandle.Create(Owner + "periodic_shift_joint_aestronglyMeasurable"),
                H("periodic shift joint aestronglyMeasurable"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive d and interval MemLp(u,2), the map (x,s) mapping to periodicExtension(d,t,u,x-s) is AE strongly measurable on windowMeasure(d,t) times Lebesgue measure."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("periodic-transport-zero-shift-joint-aestrongly-measurable"),
                DeclarationHandle.Create(Owner + "zero_shift_joint_aestronglyMeasurable"),
                H("zero shift joint aestronglyMeasurable"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary d and t and interval MemLp(u,2), the map (x,s) mapping to zeroExtension(d,t,u,x-s) is AE strongly measurable on windowMeasure(d,t) times Lebesgue measure."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("periodic-transport-l2-complex-correlation-integrable"),
                DeclarationHandle.Create(Owner + "l2_complex_correlation_integrable"),
                H("l2 complex correlation integrable"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On an arbitrary measurable type and measure, two complex MemLp 2 functions f and g have integrable Hermitian product conjugate(f(x))*g(x). The proof uses the L2 norm-product estimate and preserves complex conjugation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("periodic-transport-zerocorrelation-eq-window"),
                DeclarationHandle.Create(Owner + "zeroCorrelation_eq_window"),
                H("zeroCorrelation eq window"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary d, t, u and s, the full-line zero-extension correlation equals the original-window integral of conjugate(u(x))*zeroExtension(d,t,u,x-s). This is an exact indicator-integral identity, with no integrability premise."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("periodic-transport-zerotranslation-energy-expansion"),
                DeclarationHandle.Create(Owner + "zeroTranslationEnergy_expansion"),
                H("zeroTranslationEnergy expansion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary d and t, interval MemLp(u,2) gives zeroTranslationEnergy(d,t,u,s)=2*windowEnergy(d,t,u)-2*Re zeroCorrelation(d,t,u,s), for every real s. Both copies of the zero extension have exactly the original physical L2 mass."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("periodic-transport-periodictranslation-energy-expansion"),
                DeclarationHandle.Create(Owner + "periodicTranslationEnergy_expansion"),
                H("periodicTranslationEnergy expansion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive d, arbitrary t and interval MemLp(u,2), periodicTranslationEnergy(d,t,u,s)=2*windowEnergy(d,t,u)-2*Re periodicCorrelation(d,t,u,s), for every real s. The shift is the actual AddCircle translation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("periodic-transport-zerocorrelation-neg"),
                DeclarationHandle.Create(Owner + "zeroCorrelation_neg"),
                H("zeroCorrelation neg"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary d, t, u and s, zeroCorrelation(d,t,u,-s) is the complex conjugate of zeroCorrelation(d,t,u,s). Real correlation is consequently even; complex correlation is not assumed even."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("periodic-transport-periodiccorrelation-neg"),
                DeclarationHandle.Create(Owner + "periodicCorrelation_neg"),
                H("periodicCorrelation neg"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive d and arbitrary t, u and s, periodicCorrelation(d,t,u,-s) is the complex conjugate of periodicCorrelation(d,t,u,s). The identity follows on the actual circle by Haar translation and conjugation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("periodic-transport-correlation-difference-slice"),
                DeclarationHandle.Create(Owner + "correlation_difference_slice"),
                H("correlation difference slice"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive d and interval MemLp(u,2), the window integral of conjugate(u(x)) times the periodic-minus-zero difference at x-s equals periodicCorrelation minus zeroCorrelation at s. Integrability is proved before applying integral subtraction."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("periodic-transport-zerotranslation-energy-aestrongly-measurable"),
                DeclarationHandle.Create(Owner + "zeroTranslationEnergy_aestronglyMeasurable"),
                H("zeroTranslationEnergy aestronglyMeasurable"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary d and t and interval MemLp(u,2), the real zero-extension translation energy is AE strongly measurable as a function of the real displacement."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("periodic-transport-periodictranslation-energy-aestrongly-measurable"),
                DeclarationHandle.Create(Owner + "periodicTranslationEnergy_aestronglyMeasurable"),
                H("periodicTranslationEnergy aestronglyMeasurable"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive d, arbitrary t and interval MemLp(u,2), the real periodic translation energy is AE strongly measurable as a function of the real displacement."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("periodic-transport-zerotranslation-energy-nonneg-le"),
                DeclarationHandle.Create(Owner + "zeroTranslationEnergy_nonneg_le"),
                H("zeroTranslationEnergy nonneg le"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary d and t and interval MemLp(u,2), every zero-extension translation energy lies between zero and four times the original window L2 mass."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("periodic-transport-periodictranslation-energy-nonneg-le"),
                DeclarationHandle.Create(Owner + "periodicTranslationEnergy_nonneg_le"),
                H("periodicTranslationEnergy nonneg le"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive d, arbitrary t and interval MemLp(u,2), every periodic translation energy lies between zero and four times the original window L2 mass."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "These are transport, integrability and correlation results. They establish no "
                + "signed Weil, Schur or Robin positivity and no Riemann hypothesis conclusion.")))));
}
