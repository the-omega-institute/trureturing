using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaPntBounds;

internal sealed class MobiusPartialSumL2DivergenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/ZetaPntBounds/MobiusPartialSumL2Divergence.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal weighted Möbius partial-sum divergence.",
        H("Literal weighted Möbius partial-sum divergence"),
        Blocks(
            Paragraph(Text(
                "This unit keeps the literal finite sum over 1 ≤ n ≤ floor(x), with coefficient "
                + "the ordinary Möbius value divided by n, and the Lebesgue measure restricted to "
                + "the open half-line (1,∞). The proof uses the shifted Möbius Dirichlet series, "
                + "a general L² half-line Mellin pairing, and an unconditional nontrivial zeta-zero "
                + "witness. It does not assume RH or add a conditional certificate premise.")),
            Describe.Lean(DescribeId.Create("half-line-measure"),
                DeclarationHandle.Create(Prefix + "halfLineMeasure"),
                H("Half-line Lebesgue measure"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The measure is volume restricted to Ioi 1, exactly the domain used by the "
                    + "literal MemLp conclusion."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("literal-mobius-partial-sum"),
                DeclarationHandle.Create(Prefix + "mobiusPartialSum"),
                H("Literal weighted Möbius partial sum"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "For real x the function sums the ordinary arithmetic Möbius coefficient over "
                    + "the finite integer interval 1 ≤ n ≤ floor(x), dividing each term by n. "
                    + "No abstract transform replaces this function."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("half-line-mellin"),
                DeclarationHandle.Create(Prefix + "halfLineMellin"),
                H("General half-line Mellin functional"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "For any complex-valued function and complex parameter s, this is the "
                    + "Bochner integral of f(x) times x to the power -(s+1) over Ioi 1."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("half-line-mellin-norm-bound"),
                DeclarationHandle.Create(Prefix + "halfLineMellin_norm_le"),
                H("Sharp L² half-line Mellin norm bound"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "Every MemLp-2 function on the half-line has Mellin functional norm at most "
                    + "its L² norm divided by sqrt(2 Re(s)+1), whenever Re(s)>-1/2. The proof "
                    + "computes the exact kernel energy and applies Cauchy–Schwarz."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("half-line-mellin-differentiable"),
                DeclarationHandle.Create(Prefix + "halfLineMellin_differentiableAt"),
                H("Local differentiability of the general Mellin functional"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The Mellin functional is complex differentiable at every parameter in the "
                    + "half-plane Re(s)>-1/2. An integrable logarithmic derivative majorant supplies "
                    + "the local dominated-derivative argument."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("half-line-mellin-analytic"),
                DeclarationHandle.Create(Prefix + "halfLineMellin_analyticOnNhd"),
                H("Analyticity of the general Mellin functional"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The same general L² functional is analytic on neighborhoods throughout the "
                    + "half-plane Re(s)>-1/2."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("literal-mobius-divergence"),
                DeclarationHandle.Create(Prefix + "mobiusPartialSum_not_memLp"),
                H("Unconditional literal Möbius partial-sum L² divergence"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The theorem proves the exact unconditional negation of MemLp for the literal "
                    + "weighted Möbius partial sum on Ioi 1. The contradiction combines the shifted "
                    + "Möbius Dirichlet identity with analytic continuation of the product s·ζ(s+1) "
                    + "and the sharp half-line L² bound. A zero with real part at least one half is "
                    + "obtained unconditionally from the canonical zero data and reflection; the "
                    + "argument does not claim the Riemann hypothesis."))), DescribeRole.Theorem),
            new DocumentBlock.Section(H("Finite-prefix energy at a zeta zero"), Blocks(
            Paragraph(Text(
                "Write M(x) for the literal mobiusPartialSum defined above, and set "
                + "h(t) = exp(t/2) M(exp(t)) and "
                + "a(t) = exp(−t/2) [1 − fract(exp(t)) + ∫₀ᵗ fract(exp(u)) du]. "
                + "Let ρ be any complex zero of ζ with 1/2 ≤ β = Re(ρ) < 1, and put λ = ρ − 1/2. "
                + "For every real T ≥ 0, h² is integrable on [0,T] and, with "
                + "Kβ(T) = ∫₀ᵀ exp((2β−1)t) dt and "
                + "Cρ = 2/(1−β) + 2‖ρ‖/(1−β)², the finite-prefix estimate is "
                + "max(0, Kβ(T) − Cρ)/(400‖ρ‖⁴) ≤ ∫₀ᵀ h(t)² dt. "
                + "This includes T = 0 and β = 1/2; no global integrability assumption on h is used.")),
            Paragraph(Text(
                "The arithmetic input is the finite floor cancellation in "
                + "MoebiusLogarithmic.floor_cancellation, combined with the indicator-tail integrals "
                + "in Mertens.IntegratedExplicit.OriginalSignedJ. Expanding the two literal finite "
                + "Möbius sums gives ∫₀ᵗ a(u)h(t−u) du = t exp(−t/2) for every t ≥ 0. "
                + "Measurability and local integrability follow from the finite floor cutoffs. "
                + "The stronger public MoebiusLogarithmic.abs_reciprocalSum_le_one gives "
                + "|h(t)| ≤ exp(T/2) on [0,T], which also proves the required local integrability of h².")),
            Paragraph(Text(
                "For the complex casts aℂ and hℂ, define q(t) = 0 when t < 0 and "
                + "q(t) = exp(λt) ∫₀ᵗ aℂ(u) exp(−λu) du when t ≥ 0. "
                + "The elementary bound |a(t)| ≤ (1+t) exp(−t/2) proves genuine absolute convergence "
                + "of its damped half-line integrals before cancellation. With p = z+1/2, the "
                + "fractional Mellin identity NymanFractionalMellin.bd_mellin_base_case_proved, the change "
                + "of variables x = exp(−t), and positive convolution give "
                + "∫₀∞ aℂ(t) exp(−zt) dt = (p−1)ζ(p)/p² when Re(z) > −1/2 and p ≠ 1. "
                + "The integrability assertion also holds at p = 1, but this product formula excludes "
                + "that pole. At z = λ the strip assumptions give p = ρ ≠ 1 and hence a zero integral.")),
            Paragraph(Text(
                "Cancellation now yields the tail formula "
                + "q(t) = −exp(λt) ∫ₜ∞ aℂ(u) exp(−λu) du for t ≥ 0. "
                + "Integrating the actual envelope gives ‖q(t)‖ ≤ (2t+6) exp(−t/2). "
                + "Thus the literal zero extension is globally L¹, and its norm integral is at most "
                + "2·∫₀∞ t exp(−t/2) dt + 6·∫₀∞ exp(−t/2) dt = 2·4 + 6·2 = 20. "
                + "No assumption about the kernel on negative time enters this calculation.")),
            Paragraph(Text(
                "Set Rρ(t) = ∫₀ᵗ q(u)hℂ(t−u) du. Finite associativity is applied within the same "
                + "prefix: truncate the exponential, aℂ and hℂ to [0,t], verify their L¹ products "
                + "and the triple-integrand L¹ premise, and apply MeasureTheory.convolution_assoc'. "
                + "The arithmetic identity then reduces Rρ to an elementary exponential integral: "
                + "Rρ(t) = [exp((ρ−1/2)t) − (1+ρt) exp(−t/2)]/ρ². "
                + "Here ρ ≠ 0 follows from β ≥ 1/2. This uses no infinite transform of h at a zeta zero.")),
            Paragraph(Text(
                "Apply Analytic.Fourier.ConvolutionL2.convolution_memLp_two to q and "
                + "the function hℂ cut off to [0,T]. On [0,T] their convolution is exactly Rρ. "
                + "Restricting its nonnegative squared norm to that prefix and squaring the L¹ "
                + "norm bound gives ∫₀ᵀ ‖Rρ(t)‖² dt ≤ 20² ∫₀ᵀ h(t)² dt = 400 ∫₀ᵀ h(t)² dt. "
                + "Only the cut-off h is used as a global L² input.")),
            Paragraph(Text(
                "Let L(t) = exp((ρ−1/2)t) and D(t) = (1+ρt) exp(−t/2). "
                + "The exact local identity is "
                + "‖ρ‖⁴ ∫₀ᵀ ‖Rρ(t)‖² dt = Kβ(T) + ∫₀ᵀ ‖D(t)‖² dt "
                + "− 2∫₀ᵀ Re⟨L(t),D(t)⟩ dt. The cross term has absolute value bounded pointwise "
                + "by exp(−(1−β)t)(1+‖ρ‖t). Its doubled half-line integral equals "
                + "2/(1−β) + 2‖ρ‖/(1−β)² = Cρ. Keep the correction square in the identity, then "
                + "use its nonnegativity and the transfer bound to obtain "
                + "Kβ(T)−Cρ ≤ 400‖ρ‖⁴ ∫₀ᵀ h(t)² dt. Nonnegativity of the energy gives the maximum "
                + "with zero, and the positive denominator gives the stated estimate.")),
            Paragraph(Text(
                "This is an application of the existing arithmetic, Mellin and convolution results, "
                + "rather than a new standalone mathematical declaration. The eventual logarithmic "
                + "energy lower bound is known from Konyagin–Popov, Corollary 1, equation (9), "
                + "printed page 246, DOI 10.1007/BF02304106; no originality is claimed. "
                + "Transport by x = exp(t), the discrete identity E(N+1) = S_N, and an eventual "
                + "discrete lower bound are separate obligations. This application does not establish "
                + "those obligations, Nyman–Beurling closure, or RH."))))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Weil/ZetaPntBounds/NymanFractionalMellin")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Weil/ZeroData/UnconditionalCanonicalZeroData"))
        ]));
}
