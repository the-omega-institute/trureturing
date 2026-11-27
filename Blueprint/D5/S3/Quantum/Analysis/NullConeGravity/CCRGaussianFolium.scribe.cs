using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.NullConeGravity;

internal sealed class CCRGaussianFoliumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianFolium.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/satishchandransorce2026nulllocal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Folium sufficiency for comparable Gaussian CCR states, including degenerate symplectic forms.",
        H("Gaussian folium sufficiency"),
        Blocks(
            Paragraph(Text("Work with a Weyl system whose complex linear span is norm dense and "
                + "two normalized positive Gaussian functionals. The real datum map takes values "
                + "in the fixed space of a conjugation on a separable complex Hilbert space. "
                + "The reference symmetric covariance is the identity, the target covariance Q "
                + "is positive and injective, and the common skew operator R commutes with "
                + "conjugation. Both signed covariance operators are positive.")),
            Entry("fixed-real-inclusion", "fixedInclusion", "Inclusion of the fixed real form",
                "The real-linear inclusion sends the fixed real subspace into the original Hilbert space.",
                DescribeRole.Definition),
            Entry("real-covariance", "realCovariance", "Real covariance form",
                "Take the real part of the operator inner product on two fixed real vectors.",
                DescribeRole.Definition),
            Entry("real-symplectic-form", "realSymplecticForm", "Real symplectic form",
                "Take minus twice the real part of the skew operator inner product on fixed real vectors.",
                DescribeRole.Definition),
            Entry("fixed-real-dense", "fixedInclusion_dense", "Totality of the fixed real form",
                "Every vector is a sum of a fixed real vector and the imaginary multiple of another, "
                + "so the complex span of the fixed real form contains the whole Hilbert space."),
            Entry("extension-phase-norm", "extensionPhaseNorm", "Phase and norm of pure coordinates",
                "The signed inner product identity on fixed real vectors gives the common symplectic "
                + "phase and the required covariance norm square when both operators commute with conjugation."),
            Entry("gaussian-mutual-folium", "gaussian_mutual_excitable_of_sqrt_hs",
                "Mutual Gaussian excitability",
                "A Hilbert–Schmidt difference of the signed covariance square roots implies "
                + "both inclusions of vector folia. The common pure extension realizes the "
                + "two signed covariances on a common real phase space. The Hilbert–Schmidt "
                + "difference of the doubled covariances admits square-summable squeeze "
                + "parameters in either order. For each direction, the squeezed vector "
                + "is transported to a Hilbert basis split across the closed complex span "
                + "of the embedded data and its orthogonal complement. Occupation splitting "
                + "gives a countable family of vectors in the first Fock space with squared "
                + "norms summing to one and Weyl matrix coefficients summing to the target "
                + "characteristic function. Gram equality of cyclic Weyl vectors and "
                + "coherent totality give the intertwining unitary from the reference GNS "
                + "space. The basis split and enumeration also apply to finite or empty "
                + "basis sets. The resulting vectors therefore realize excitability on "
                + "the full algebra, including a nontrivial symplectic radical."),
            Entry("gaussian-folium", "gaussian_excitable_of_sqrt_hs",
                "Gaussian folium sufficiency",
                "Under the same covariance, characteristic-function and Hilbert–Schmidt "
                + "hypotheses, the target state is excitable in the reference GNS representation."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(statement))), role);
}
