using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Gauge;

internal sealed class PatiSalamUnification4DDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Gauge/PatiSalamUnification4D.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/LieTheory/patisalam1974lepton");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The fourth color, the half-spin generation, and the orthogonal vector action.",
        H("Pati–Salam unification in four dimensions"),
        Blocks(
            Paragraph(Text("The fourth color is the lepton. Its different color charge separates the off-diagonal blocks of the adjoint and fixes the hypercharge of each member of the left-handed generation. The vector action combines the real exterior square and the quaternion representation.")),
            Entry("fourth-color", "bMinusLGen", "Baryon number minus lepton number",
                "The first three diagonal entries are one third. The fourth is minus one.", DescribeRole.Definition),
            Entry("normalization", "su4_bMinusL_traceless_and_norm", "Fourth-color generator normalization",
                "The trace vanishes, the trace of the square is four thirds, and multiplying by the square root of three eighths brings the quadratic trace to one half."),
            Entry("color-commutator", "su4_sm_subalgebra_commute", "Color and baryon minus lepton commute",
                "The generator is scalar on the three color coordinates, so its commutator with the color block vanishes."),
            Entry("compact-embedding", "su4_sm_embedding", "Compact color and abelian Lie embedding",
                "A traceless skew-Hermitian color block and an imaginary multiple of the baryon-minus-lepton generator define an injective real Lie algebra map into the traceless skew-Hermitian four by four matrices."),
            Entry("adjoint-blocks", "su4_adjoint_decomposition", "Adjoint block decomposition",
                "Each traceless four by four complex matrix has unique coordinates in a color octet, a singlet, a column and a row. The complex dimensions are eight, one, three and three."),
            Entry("adjoint-charges", "su4_adjoint_leptoquark_bMinusL", "Charges of the adjoint blocks",
                "The commutator with the diagonal generator has eigenvalue zero on the two diagonal blocks, four thirds on the upper-right column, and minus four thirds on the lower-left row."),
            Entry("irreducible-blocks", "su4_adjoint_blocks_irreducible", "Irreducibility of the summands",
                "The traceless color block carries its adjoint action. The column and row carry the fundamental and dual actions. The remaining summand is one-dimensional."),
            Entry("left-right-counts", "ps16_left_right_dims", "Left-handed Weyl state counts",
                "The color fundamental with left weak weight contributes eight states. The color antifundamental with right weak weight contributes a further eight."),
            Entry("cancellation", "ps16_anomalies_vanish", "Linear and cubic charge traces",
                "The left and right weak weights sum to zero. The baryon-minus-lepton, hypercharge, electric charge, and specified mixed and cubic traces also vanish."),
            Entry("matching", "ps16_traces_and_gut_matching", "Quadratic traces and coupling matching",
                "The squared left and right weak weights each sum to two. The square of half the baryon-minus-lepton weight sums to four thirds. Hypercharge and electric charge have quadratic traces ten thirds and sixteen thirds. At equal positive Pati–Salam couplings, the normalized couplings agree and the weak mixing fraction is three eighths."),
            Entry("half-spin-weights", "ps16_matches_so10_spinor16", "Even half-spin weight correspondence",
                "An explicit permutation of the sixteen weight labels preserves both weak weights, baryon minus lepton, hypercharge, and electric charge."),
            Entry("block-embedding", "so6SO4ToSO10_injective", "Embedding of the oriented blocks",
                "The two diagonal blocks are recovered by restricting both matrix indices to their respective summands."),
            Entry("orthogonal-action", "patiSalamToSO10_special_orthogonal", "Ten-dimensional special orthogonal action",
                "The exterior-square and quaternion blocks act on orthogonal summands. Each preserves the Euclidean form and orientation."),
            Entry("multiplication", "patiSalamToSO10_hom", "Multiplicativity",
                "Componentwise multiplication in the three factors gives matrix multiplication in the direct-sum action."),
            Entry("central-kernel", "patiSalamToSO10_kernel", "Central kernel",
                "An element acts identically exactly when its color factor is one of the two scalar signs and its two weak factors have a common scalar sign."),
            Entry("quotient-embedding", "patiSalamQuotientToSO10_injective", "Faithful quotient action",
                "Quotienting the three factors by the four central elements in the kernel gives an injective map into the ten-dimensional special orthogonal group."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(statement))), role);
}
