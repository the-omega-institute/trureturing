using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Semigroups;

internal sealed class WuQubitSharpTwoPhysicalDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Semigroups/WuQubitSharpTwoPhysical.";
    private static readonly LibraryNoteRef Wu = LibraryNoteRef.Create("D5/L/SpinModels/wu2026sharp");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Physical one-mode exact affinity optimality, two-entropy equality, and tracial stability for all complex qubit densities of trace one.",
        H("Physical one-mode rigidity at exponent two"),
        Blocks(
            Paragraph(Text("For any real h let a = exp(h)/(2 cosh h), b = exp(−h)/(2 cosh h), D = diag(a,b). " +
                "The positive Heisenberg generator L in Wu arXiv:2610.33686v1, (3.2), has diagonal entries " +
                "2b(X₀₀−X₁₁), 2a(X₁₁−X₀₀), and off-diagonal entries X₀₁, X₁₀. " +
                "For a complex positive semidefinite 2×2 matrix ρ of ordinary trace one, put X = D^(−1/4) ρ^(1/2) D^(−1/4). " +
                "Define E(h,ρ) = Re Tr(ρ^(1/2) D^(1/4) L(X) D^(1/4)) and H(h,ρ) as the ordinary-trace " +
                "relative entropy of ρ with respect to D, with the zero-eigenvalue entropy convention. " +
                "Both spectral slots carry their multiplicities. Let v = |λ₀−λ₁| and z be the expectation of diag(1,−1) " +
                "in the chosen unit eigenvector for the larger eigenvalue, choosing column zero when they coincide.")),
            Paragraph(Text("Write A(h,ρ) = Re Tr(ρ^(1/2) gibbs(h)^(1/2)) for the ordinary-trace square-root affinity. " +
                "The overlap identity holds for every real h and every complex PSD trace-one ρ. The exact affinity lower bound, " +
                "its strictness, and physical optimality are stated for h ≥ 0 over the same PSD trace-one class, including rank-one and repeated spectra.")),
            Entry("energy-entropy-eq", "energy_entropy_eq", "Exact ordinary-trace reduction",
                "For every real h and every complex positive semidefinite trace-one qubit ρ, E(h,ρ) = normalizedEnergy(h,v,z) " +
                "and H(h,ρ) = normalizedEntropy(h,v,z) of WuQubitSharpTwoRigidity. These specialize (3.6)–(3.7) at p = p' = 2. " +
                "The proof uses the paired modular edge identity generatorTrace_eq_cosh with the signed rates a,b and D J D⁻¹ = (a/b)J for J = |0⟩⟨1|, " +
                "together with the existing ordinary-trace matrix relative entropy and the two-slot unitary frame identities. It covers rank one and the repeated spectrum."),
            Entry("sharp-physical-deficit", "sharp_physical_deficit", "Physical sharp deficit and exact equality",
                "For h ≥ 0 and every complex positive semidefinite trace-one qubit ρ, E(h,ρ)−c(h)H(h,ρ) ≥ 0, " +
                "with c(h) the coefficient of WuQubitSharpTwoRigidity. Equality holds if and only if v = tanh h and (h = 0 or z = 1). " +
                "The conditions express the Gibbs spectrum and, at positive h, its alignment with the Gibbs axis."),
            Entry("tracial-stability", "tracial_stability", "Physical tracial affinity lower bound",
                "For every complex positive semidefinite trace-one qubit ρ, let W = Re Tr(ρ^(1/2))/√2, " +
                "the affinity to I/2. Then (4/3)(1−W)² ≤ E(0,ρ)−H(0,ρ)/2. " +
                "The ordinary trace of the square root gives the exact scalar affinity √((1+√(1−v²))/2) and the scalar stability theorem supplies the bound."),
            Entry("tracial-stability-strict", "tracial_stability_strict", "Strict tracial stability at distinct eigenvalues",
                "For every complex positive semidefinite trace-one qubit ρ with v > 0, " +
                "(4/3)(1−W)² < E(0,ρ)−H(0,ρ)/2. This includes rank one."),
            Entry("exact-affinity-overlap", "trace_sqrt_gibbs_eq", "Exact physical square-root affinity coordinate",
                "For every real h and every complex positive semidefinite trace-one qubit ρ, " +
                "A(h,ρ) = (1 + t k(h) z)/√((1+t²)(1+k(h)²)), where t = v/(1+spectralRoot(v)) and k(h) = thermalBias(h). " +
                "This is the ordinary-trace overlap of the two positive square roots and covers rank-one and repeated spectra."),
            Entry("exact-affinity-stability", "exact_affinity_stability", "Exact affinity stability on physical states",
                "For h ≥ 0 and every complex positive semidefinite trace-one qubit ρ, " +
                "exactAffinityCoefficient(h)(1−A(h,ρ))² ≤ E(h,ρ)−sharpCoefficient(h)H(h,ρ). " +
                "The coefficient is the exact one-mode constant from WuQubitSharpTwoExactAffinity."),
            Entry("exact-affinity-stability-strict", "exact_affinity_stability_strict", "Strict physical affinity stability away from Gibbs",
                "For h ≥ 0 and every complex positive semidefinite trace-one qubit ρ distinct from gibbs(h), " +
                "the exact affinity inequality is strict. The conclusion includes faithful states, rank-one states, and the repeated-spectrum case."),
            Entry("exact-affinity-coefficient-greatest", "exact_affinity_coefficient_isGreatest", "Physical saturation by faithful states",
                "For h ≥ 0, exactAffinityCoefficient(h) is the greatest c for which the physical affinity inequality holds for every complex positive semidefinite trace-one qubit ρ. " +
                "The coefficient is admissible for the full class. The deficit-to-squared-defect quotient approaches it along faithful positive-definite trace-one states realizing the sharp scalar path."),
            Paragraph(Text("At h = 0 the coefficient is 4/3. " +
                "Wu's multimode or collective logarithmic-Sobolev optimality is related research beyond these one-mode formal statements. " +
                "Remark 3.15 of Wu leaves (3.54) conditional for arbitrary signs and general exponents. The present result gives quantitative stability at exponent two in one mode, including at positive temperature.")))));

    private static DocumentBlock Entry(string id, string declaration, string title, string claim) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Wu),
            Blocks(Paragraph(Text(claim))), DescribeRole.Theorem);
}
