using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Gauge;

internal sealed class LatticeReflectionPositivity4DDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.";
    private static LibraryNoteRef Reflection => LibraryNoteRef.Create("D5/L/LieTheory/jaffejanssens2017reflection");
    private static LibraryNoteRef Ising => LibraryNoteRef.Create("D5/L/SpinModels/wegner2014generalizedising");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Wilson reflection positivity and planar Wilson loops in the two-element gauge theory.",
        H("Reflection positivity and Wilson loops on finite lattices"),
        Blocks(
            Paragraph(Text(
                "For a real kernel K on two copies of a finite set X, the reflection pairing of f and g "
                + "is Σₓ Σᵧ K(x,y) overline(f(y)) g(x). Reflection exchanges the copies and conjugates "
                + "the value of the first observable.")),
            Paragraph(Text(
                "For every real weight w on X, the pairing of f with itself for K(x,y) = w(x)w(y) equals "
                + "the squared norm of Σₓ w(x) f(x), regarded as a complex number.")),
            Node("power-reflection-positivity", "factorized_interaction_pow_rp", "Powers of the interaction",
                "For finitely many complex features Aᵢ and real coefficients cᵢ ≥ 0, put "
                + "V(x,y) = Σᵢ cᵢ Re(Aᵢ(x) overline(Aᵢ(y))). For every natural n, the pairing of f "
                + "with itself for w(x)w(y)V(x,y)ⁿ is real and nonnegative. Real and imaginary parts "
                + "give real features and the product expansion gives the features for each power."),
            Node("exponential-reflection-positivity", "exponential_boltzmann_reflection_positivity",
                "Exponential reflection positivity",
                "For every real half action S and β ≥ 0, the diagonal pairing with weight "
                + "w(x)w(y) exp(β(S(x) + S(y) + V(x,y))) is real and nonnegative. Multiplying the "
                + "product weights by exp(β S) incorporates both half actions. The exponential "
                + "series then gives a convergent sum of the nonnegative power pairings.", Reflection),
            Node("sharp-coupling-range", "exponential_boltzmann_rp_iff", "The exact coupling range",
                "At fixed β, the diagonal pairing is real and nonnegative for all finite half "
                + "spaces, finite feature families with nonnegative coefficients, real weights "
                + "and half actions, and complex observables, exactly when β ≥ 0. On two points "
                + "take f(false) = −1 and f(true) = 1. Use f as the single feature with coefficient "
                + "one, unit weights and zero half action. The pairing is the real number 4 sinh β, "
                + "which is strictly negative for every β < 0."),
            Paragraph(Text(
                "The Wilson lattice has two open time halves of length T. Each time slice is the "
                + "three-dimensional torus of side L, with T and L positive. Local transformations "
                + "send an oriented link U from v to w to g(v) U g(w)⁻¹. Each plaquette contributes "
                + "the real trace of the represented holonomy. The full pairing divides the weighted "
                + "counting sum by the strictly positive full Wilson partition function Z. "
                + "After fixing the crossing links, the half-configuration sum is multiplied by |G|^(L³)/Z.")),
            Paragraph(Text(
                "Local transformations conjugate each plaquette holonomy at its starting site. "
                + "Cyclicity preserves the trace, and summing the individual real traces preserves "
                + "the Wilson action on spatial, internal time-space and crossing plaquettes. "
                + "Orient each crossing link from the negative to the positive half. The gauge "
                + "that is one on the negative half and U₀(x) above x on the positive half sends "
                + "U₀(x) to one and applies a bijection to the half configurations.")),
            Node("temporal-gauge-fixing", "temporal_gauge_fixing", "Counting in temporal gauge",
                "For any gauge-invariant summand with values in an additive commutative monoid, "
                + "the full sum equals |G|^(L³) times the sum with unit crossing links. The "
                + "bijection of half configurations applies separately for each crossing field."),
            Paragraph(Text(
                "When crossing links are one, the crossing plaquette holonomy is U₊ U₋⁻¹ for the "
                + "paired spatial links at the cut. Its real trace is the sum over row and column "
                + "indices of Re(rep(U₊)ₐᵦ overline(rep(U₋)ₐᵦ)).")),
            Node("wilson-reflection-positivity", "lattice_ym_4d_reflection_positivity",
                "Reflection positivity of the four-dimensional Wilson action",
                "For a finite gauge group, a unitary representation on a finite complex coordinate "
                + "space, β ≥ 0, and a gauge-invariant positive-half observable F, the normalized "
                + "reflection pairing of F with itself is real and nonnegative. In the gauge with "
                + "unit crossing links, the crossing plaquette contributions are precisely the "
                + "interaction features of the exponential theorem.", Reflection),
            Node("wilson-cauchy-schwarz", "lattice_ym_4d_cauchy_schwarz",
                "Cauchy–Schwarz for the physical pairing",
                "For β ≥ 0 and two gauge-invariant positive-half observables F and H, the squared norm of "
                + "their reflection pairing is bounded by the product of the real diagonal pairings "
                + "of F and H."),
            Paragraph(Text(
                "For every real β and s equal to 1 or −1, exp(βs) = cosh(β)(1 + s tanh(β)).")),
            Paragraph(Text(
                "For every real β, the finite normalized Wilson expectation equals the sum of "
                + "tanh(β)^|S| over surfaces with the prescribed boundary divided by the sum over "
                + "closed surfaces. The parity character sum eliminates all other surfaces.")),
            Node("wilson-loop-2d", "wilson_loop_2d_exact_area_law", "Exact Wilson-loop area law in two dimensions",
                "An R by T rectangular loop in an open M by N lattice has one plaquette filling. "
                + "For every real β the expectation equals tanh(β)^(R T). For β > 0 the string tension "
                + "σ = −log(tanh(β)) is positive and the same expectation equals exp(−σ R T).", Ising),
            Node("hypercubic-filling-area", "hypercubic_4d_minimal_surface_area_bound",
                "Area of a four-dimensional plaquette filling",
                "Every plaquette filling of an R by T planar rectangle in an open four-dimensional "
                + "box contains at least R T plaquettes. Summing the boundary along an in-plane link "
                + "ray, over all transverse coordinates, forces an odd number of in-plane plaquettes "
                + "above each elementary square of the rectangle."),
            Node("strong-coupling-4d", "strong_coupling_4d_minimal_surface_expansion_bound",
                "Four-dimensional strong-coupling bound",
                "Fix an open four-dimensional box and an R by T planar rectangle in it. For β ≥ 0 "
                + "the Wilson expectation is between zero and the sum of tanh(β)^|M| over inclusion-minimal "
                + "fillings M in that same box. Every exponent |M| is at least R T. Choosing a minimal "
                + "subfilling and its disjoint closed complement determines the original filling. "
                + "The closed-surface sum cancels."))));

    private static DocumentBlock Node(string id, string name, string title, string prose,
        params LibraryNoteRef[] sources) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(sources),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
