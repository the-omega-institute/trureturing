using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Gauge;

internal sealed class LatticeReflectionPositivity4DDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D.";
    private const string Literature = "D5/L/HilbertOperators/osterwalderseiler1978lattice";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gauge invariance, Osterwalder–Schrader positivity, positive transfer, and the strong-coupling area law in four-dimensional Wilson lattice gauge theory.",
        H("Four-dimensional Wilson lattice gauge theory"),
        Blocks(
            Paragraph(Text("The open four-dimensional box consists of two copies of a half-box "
                + "and a temporal seam. Each copy uses distance from the seam as its time coordinate. "
                + "The gauge representation is finite dimensional, unitary and measurable.")),
            Result("plaquette-gauge-invariance", "wilson_plaquette_gauge_invariant",
                "Local gauge invariance of plaquette weights",
                "In an interior plaquette, the endpoint factors from the four link transformations "
                + "cancel at each intermediate vertex. The residual conjugation leaves the trace "
                + "and its real part unchanged."),
            Result("seam-plaquette-gauge-invariance", "wilson_seam_plaquette_gauge_invariant",
                "Gauge invariance at the seam",
                "On a plaquette crossing the reflection plane, site gauges transform each seam link "
                + "at its negative and positive endpoints. The four resulting endpoint factors "
                + "cancel except for conjugation at the starting site."),
            Result("action-gauge-invariance", "wilson_action_gauge_invariant",
                "Gauge invariance of the Wilson action",
                "The same cancellation holds on every seam plaquette when each seam link "
                + "transforms by the site gauges on both halves. Summing gives gauge invariance "
                + "of the full Wilson action."),
            Result("reflection-invariance", "wilson_action_reflection_invariant",
                "Time reflection of the Wilson action",
                "Time reflection swaps the two halves and inverts the seam links. The two interior "
                + "actions are interchanged. Each seam holonomy is conjugate to the inverse of its "
                + "original value, which preserves its real trace."),
            Result("reflection-positivity", "wilson_reflection_positivity",
                "Osterwalder–Schrader reflection positivity",
                "For every integrable complex observable of one half and every nonnegative coupling, "
                + "the Wilson expectation of the reflected conjugate times the observable is a "
                + "nonnegative real. Use two independent Haar boundary gauges and replace the seam "
                + "gauge by their relative gauge. The crossing action is then a real dot product "
                + "of the real and imaginary matrix entries. Each term of its exponential series "
                + "integrates to a sum of squared moduli with nonnegative coefficients. The uniform "
                + "bound on the crossing action supplies an integrable majorant. The Haar change "
                + "of variables applies to gauge-variant as well as gauge-invariant observables."),
            Result("os-class-norm", "wilson_os_norm",
                "Norm of a physical class",
                "Split each half configuration into its boundary links and its other links. "
                + "Integrate the observable over the other links with the remainder of the half action "
                + "as weight. The boundary kernel induces a pre-inner product on the reduced "
                + "observables, and quotienting by its null space gives the physical pre-Hilbert space. "
                + "The class norm is the square root of the unnormalized reflected expectation."),
            Result("os-seminorm", "wilson_os_seminorm",
                "Normalized Osterwalder–Schrader seminorm",
                "Divide the physical class norm by the square root of the positive Wilson partition "
                + "function. This defines a seminorm on integrable half observables, equal to the "
                + "square root of the real part of the normalized diagonal Gibbs pairing."),
            Result("os-pairing", "wilson_os_pairing",
                "Mixed Gibbs pairing on the physical quotient",
                "For two integrable half observables, the inner product of their physical classes "
                + "equals the mixed Gibbs pairing multiplied by the Wilson partition function. "
                + "Splitting the action into the boundary step and two half remainders gives the "
                + "identity by integration over the two interiors."),
            Result("os-cauchy-schwarz", "wilson_os_cauchy_schwarz",
                "Cauchy–Schwarz for the mixed Gibbs pairing",
                "The absolute value of the normalized mixed Gibbs pairing is bounded by the "
                + "product of the two normalized Osterwalder–Schrader seminorms."),
            Result("positive-transfer", "wilson_physical_transfer_nonneg",
                "Positivity of the one-step transfer operator",
                "The integral operator with the Wilson boundary kernel descends to the physical "
                + "quotient. Its quadratic form on each class is the boundary Haar integral of "
                + "the squared modulus of the transferred representative, so it is nonnegative."),
            Result("finite-component-bound", "wilson_strong_coupling_finite_bound",
                "Finite-volume rooted-component bound",
                "For a unitary representation of positive dimension with a nontrivial scalar "
                + "central character, expand each plaquette weight into one plus its activity. "
                + "Mark a link of the rectangular loop and group plaquettes by the component "
                + "rooted at that link. Central Haar changes of variables cancel the components "
                + "that fail to cover a cell under projection onto the rectangle. The norm is "
                + "bounded by the sum of the surviving activity bounds and also by one."),
            Result("finite-geometric-bound", "wilson_strong_coupling_geometric_finite_bound",
                "Finite geometric bound",
                "A component covering all cells has at least R times T plaquettes and at most "
                + "the total number of plaquettes in the box. Each link is incident to at most six "
                + "plaquettes and each plaquette has at most twenty neighbors. Counting the rooted "
                + "components and bounding each activity by exp(beta times d) minus one gives a "
                + "finite geometric sum with ratio q equal to eighty times that activity bound."),
            Result("uniform-area-law", "wilson_strong_coupling_area_bound",
                "Volume-uniform strong-coupling area law",
                "For nonnegative coupling beta, positive rectangle sides R and T, and q less than "
                + "one, the norm of the normalized rectangular Wilson loop expectation is at most "
                + "6 q^(R T) / (80 (1 - q)), where q = 80 (exp(beta d) - 1) and d is the "
                + "representation dimension. "
                + "The same estimate applies to every open box containing the rectangle. The "
                + "nontrivial scalar central character is used in the cancellation."))));

    private static DocumentBlock Result(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Literature)),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
