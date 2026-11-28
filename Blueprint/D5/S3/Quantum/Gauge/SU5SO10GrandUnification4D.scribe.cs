using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Gauge;

internal sealed class SU5SO10GrandUnification4DDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.";
    private static readonly LibraryNoteRef SU5 =
        LibraryNoteRef.Create("D5/L/LieTheory/georgiglashow1974unity");
    private static readonly LibraryNoteRef Spin10 =
        LibraryNoteRef.Create("D5/L/LieTheory/fritzschminkowski1975unified");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unified gauge generators, adjoint and fermion weights, and chiral spinor charges.",
        H("Special unitary and orthogonal unification"),
        Blocks(
            Paragraph(Text("The fundamental coordinates consist of a color triple and a weak pair. The Hermitian convention gives the hypercharge weights minus one third on color and one half on the weak pair. Matrix commutators measure differences of weights, while the second exterior power adds the weights of its two factors.")),
            Entry("sm-embedding", "smEmbedding", "Embedded gauge generators",
                "The color and weak matrices occupy disjoint diagonal blocks. The remaining summand is the normalized hypercharge matrix multiplied by an arbitrary real coefficient.", DescribeRole.Definition, SU5),
            Entry("traceless-hermitian", "su5_embedding_traceless_hermitian", "Traceless Hermitian embedding",
                "For traceless Hermitian color and weak inputs and any real hypercharge coefficient, their embedded sum has zero trace and is Hermitian.", DescribeRole.Theorem, SU5),
            Entry("embedding-injective", "su5_sm_embedding_injective", "Recovery of the gauge generators",
                "Equal embedded matrices with traceless color inputs have equal color matrices, equal weak matrices, and equal real hypercharge coefficients.", DescribeRole.Theorem),
            Entry("commuting-blocks", "su5_sm_blocks_commute", "Commuting gauge factors",
                "The color and weak embeddings commute for arbitrary input matrices. Both commute with the hypercharge generator in its normalized and unnormalized forms.", DescribeRole.Theorem),
            Entry("trace-normalization", "su5_trace_normalization", "Gauge generator normalization",
                "The squared traces of the normalized hypercharge generator, the third weak generator, and the eighth color generator all equal one half. The squared trace of unnormalized hypercharge is five sixths, so its ratio to the weak squared trace is five thirds.", DescribeRole.Theorem, SU5),
            Entry("electric-charge", "su5_electric_charge_traceless", "Fundamental electric charge",
                "The electric charge diagonal contains three copies of minus one third followed by one and zero, and its trace vanishes.", DescribeRole.Theorem, SU5),
            Entry("weak-mixing-angle", "su5_weinberg_angle_from_trace", "Weak mixing angle at unification",
                "The electric squared trace is four thirds. Dividing the weak squared trace by it gives three eighths.", DescribeRole.Theorem),
            Entry("adjoint-decomposition", "su5_adjoint_decomposition", "Unique adjoint decomposition",
                "Every traceless five by five matrix has unique traceless color and weak components, one hypercharge scalar, and two rectangular components.", DescribeRole.Theorem, SU5),
            Entry("adjoint-dimensions", "su5_adjoint_dimensions", "Adjoint component dimensions",
                "The color and weak traceless spaces have dimensions eight and three. Each rectangular space has dimension six. Together with the hypercharge line the full traceless space has dimension twenty-four.", DescribeRole.Theorem),
            Entry("adjoint-block-action", "su5_adjoint_block_action", "Action on the adjoint components",
                "Commutation with a block-diagonal generator gives the color and weak commutators and zero hypercharge scalar. Each rectangle receives left multiplication by its row generator, negative right multiplication by its column generator, and a hypercharge term with coefficient minus or plus five sixths of the generator parameter.", DescribeRole.Theorem),
            Entry("adjoint-irreducibility", "su5_adjoint_blocks_irreducible", "Irreducibility of the adjoint components",
                "For either traceless square block, an invariant subspace contained in the trace-zero space is zero or the whole trace-zero space. For either rectangle, stability under the left and right traceless matrices forces the same alternatives. The hypercharge line is one-dimensional.", DescribeRole.Theorem),
            Entry("adjoint-hypercharge", "su5_adjoint_hypercharge_eigenvalues", "Adjoint hypercharge weights",
                "For each matrix unit the hypercharge commutator is the unit multiplied by its row weight minus its column weight. The two diagonal blocks have weight zero, the color to weak block has weight minus five sixths, and the weak to color block has weight plus five sixths.", DescribeRole.Theorem, SU5),
            Entry("leptoquark-charge", "su5_leptoquark_electric_charges", "Off-diagonal electric charges",
                "For each color, the electric charge commutator has eigenvalues minus four thirds and minus one third on the two color to weak units. The reversed units have eigenvalues plus four thirds and plus one third.", DescribeRole.Theorem, SU5),
            Entry("dual-action", "dualAction", "Dual generators",
                "The dual infinitesimal action is the negative transpose.", DescribeRole.Definition, SU5),
            Entry("wedge-action", "exteriorAction", "Second exterior-power generators",
                "The infinitesimal generator acts on both slots of a wedge pair by the exterior product rule.", DescribeRole.Definition, SU5),
            Entry("wedge-coordinates", "wedgeCoords", "Coordinates of an exterior pair",
                "Each entry is the two by two minor of the pair of vectors at the corresponding ordered indices.", DescribeRole.Definition),
            Entry("wedge-product-rule", "su5_exterior_product_rule", "Exterior product rule",
                "For any fundamental matrix and any pair of vectors, the exterior action on their wedge is the sum of the two wedges obtained by acting on one vector at a time.", DescribeRole.Theorem),
            Entry("fermion-actions", "su5_fermion_weight_actions", "Induced diagonal actions",
                "On the dual each diagonal entry changes sign. On the second exterior power the diagonal entry of an ordered pair is the sum of the two selected entries.", DescribeRole.Theorem),
            Entry("fermion-state-count", "su5_bar5_plus_10_dim", "Number of Weyl states",
                "The complex space indexed by the five dual coordinates and ten wedge coordinates has dimension fifteen.", DescribeRole.Theorem),
            Entry("fermion-hypercharges", "su5_bar5_plus_10_matches_sm_hypercharges", "One-generation charges and traces",
                "The induced hypercharge and third weak weight agree with the Standard Model tables in all fifteen slots. The first and third hypercharge moments vanish, the second is ten thirds, and the two mixed color and weak hypercharge sums vanish.", DescribeRole.Theorem),
            Entry("general-cubic-anomaly", "suN_antisym_cubic_anomaly", "Cubic trace of the exterior square",
                "For a traceless real Cartan vector in any dimension, the sum of the cubes of the pair weights equals the fundamental cubic trace multiplied by the dimension minus four.", DescribeRole.Theorem),
            Entry("cubic-anomaly", "su5_cubic_anomaly_cancellation", "Opposite cubic traces",
                "For a real traceless Cartan vector the exterior square contributes the fundamental cubic trace. The dual contributes its negative. Their sum is zero.", DescribeRole.Theorem, SU5),
            Entry("b-minus-l-conservation", "su5_b_minus_l_conserved", "Baryon minus lepton charge at gauge vertices",
                "In either fermion representation, a matrix unit with a nonzero action coefficient carries the outgoing minus incoming baryon minus lepton charge. The adjoint assignment is four fifths of the adjoint hypercharge and equals plus or minus two thirds on the off-diagonal gauge units.", DescribeRole.Theorem),
            Entry("group-inclusion", "su5ToSo10", "Real orthogonal action",
                "The special unitary action on five complex coordinates gives a multiplicative special orthogonal action on ten real coordinates by taking real and imaginary blocks.", DescribeRole.Definition, Spin10),
            Entry("faithful-group-inclusion", "su5_to_so10_injective", "Faithful real orthogonal action",
                "The real orthogonal action determines the original special unitary matrix.", DescribeRole.Theorem),
            Paragraph(Text("The half-spin weight model uses five occupation bits. Even occupations have degrees zero, two, and four with respective counts one, ten, and five. The shift by minus half the trace gives a sum of occupied weights on the traceless Cartan. The degree-four weight equals minus the missing coordinate. The cubic trace of the sixteen even weights vanishes for every real Cartan vector, and the five charge assignments are evaluated in every slot.")),
            Entry("spinor-branching", "so10_su5_fermion_branching", "Traceless Cartan branching",
                "For every real traceless Cartan vector, the even spinor weights in order equal the neutral singlet followed by the fifteen dual and exterior weights.", DescribeRole.Theorem, Spin10),
            Entry("spinor-b-minus-l", "so10_su5_b_minus_l_compatibility", "Spinor baryon minus lepton matching",
                "The empty occupation has baryon minus lepton charge one. Each other slot has the charge induced from its exterior pair or missing dual coordinate.", DescribeRole.Theorem, Spin10))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement,
        DescribeRole role, LibraryNoteRef? source = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(),
            source is null ? AssessedProvenance.FromRepo() : AssessedProvenance.FromRepo(source),
            Blocks(Paragraph(Text(statement))), role);
}
