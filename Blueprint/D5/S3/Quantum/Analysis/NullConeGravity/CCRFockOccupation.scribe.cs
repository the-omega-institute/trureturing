using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.NullConeGravity;

internal sealed class CCRFockOccupationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Analysis/NullConeGravity/CCRFockOccupation.";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/satishchandransorce2026nulllocal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The occupation model of bosonic Fock space, its coherent Gram formula, and totality on real subspaces.",
        H("Bosonic occupation space and coherent vectors"),
        Blocks(
            Paragraph(Text("A Hilbert basis labels the modes of the one-particle space. "
                + "The occupation model uses square-summable amplitudes indexed by finite configurations of these modes. "
                + "Coherent vectors supply the cyclic subspaces used in Gaussian representations of the Weyl relations.")),
            Entry("occupation", "Occupation", "Finite occupations",
                "An occupation is a finitely supported function from the mode index type to the natural numbers.",
                DescribeRole.Definition),
            Entry("boson-fock", "BosonFock", "Bosonic Fock space",
                "Take the complex square-summable families indexed by finite occupations.", DescribeRole.Definition),
            Entry("vacuum", "fockVacuum", "Vacuum vector",
                "The amplitude at the zero occupation is one and every other amplitude is zero.",
                DescribeRole.Definition),
            Entry("coherent-exponential", "fockExponential", "Coherent exponential vector",
                "The coherent vector of z has one factor per occupied mode, given by its Hilbert-basis coordinate "
                + "raised to its occupation number and divided by the square root of that number's factorial.",
                DescribeRole.Definition),
            Entry("vacuum-norm", "fockVacuum_norm", "Unit vacuum norm",
                "The single nonzero vacuum amplitude gives norm one."),
            Entry("coherent-coordinate", "fockExponential_apply", "Coherent occupation amplitude",
                "At each occupation the amplitude is the product of the indicated factorial-normalized powers. "
                + "The empty product gives amplitude one at the zero occupation."),
            Entry("zero-coherent", "fockExponential_zero", "The coherent vector at zero",
                "At zero one-particle input the coherent vector equals the vacuum."),
            Entry("coherent-gram", "fockExponential_inner", "Coherent Gram identity",
                "The inner product of the coherent vectors of z and w is exp(⟨z, w⟩) in the antilinear-first "
                + "convention. On a finite set of modes the sum factors into single-mode exponential series. "
                + "Absolute summability lets the finite-mode sums converge to the occupation-space inner product."),
            Entry("coherent-norm", "fockExponential_norm_sq", "Squared coherent norm",
                "The squared norm of the coherent vector of z is exp(‖z‖²), by the diagonal Gram identity."),
            Entry("coherent-continuity", "fockExponential_continuous", "Norm continuity of coherent vectors",
                "The Gram identity expresses the squared norm of a difference of coherent vectors as a "
                + "continuous function of the inputs which vanishes when the inputs agree."),
            Entry("coherent-totality", "fockExponential_dense_span", "Totality of coherent vectors",
                "The complex linear span of all coherent exponential vectors is dense. Restrict a vanishing "
                + "coherent pairing to finitely many coordinates and use uniqueness of the scalar power-series "
                + "coefficients to recover the amplitude at every finite occupation."),
            Entry("real-coherent-totality", "fockExponential_dense_span_of_dense_real",
                "Totality over a real subspace with dense complex span",
                "If a real-linear subspace has dense complex span in the one-particle space, its coherent "
                + "vectors already have dense complex span in Fock space. Pairing with a fixed Fock vector "
                + "is holomorphic along affine complex lines by locally uniform convergence of finite occupation sums. "
                + "Every vector in the complex span has the form x + iy with x and y in the real subspace. "
                + "A pairing that vanishes on that subspace vanishes along the whole line x + cy by the identity "
                + "theorem. Continuity and coherent totality then force the Fock vector to vanish."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(statement))), role);
}
