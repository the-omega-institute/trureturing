using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Lorentz;

internal sealed class HodgeChiralLieDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Lorentz/HodgeChiralLie.";
    private static LibraryNoteRef Jacobson => LibraryNoteRef.Create("D5/L/LieTheory/jacobson1995thermodynamics");
    private static LibraryNoteRef Urbantke => LibraryNoteRef.Create("D5/L/LieTheory/urbantke1984plebanski");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The real Lorentz matrix Lie algebra has a Pauli realization and its complexification splits into Hodge eigenspaces.",
        H("Lorentz Lie algebra and chiral Hodge decomposition"),
        Blocks(
            Paragraph(Text("The metric has signature (−,+,+,+). The oriented pair order is (01,02,03,23,31,12). "
                + "The same Lorentz signature fixes the null directions used in local horizon geometry. "
                + "Index lowering identifies Lorentz endomorphisms with covariant two-forms.")),
            Definition("eta", "eta", "The Lorentz metric", "The diagonal entries of the four-by-four metric are minus one followed by three ones."),
            Definition("lorentz-lie", "lorentzLie", "Lorentz matrices",
                "The carrier is the Lie subalgebra of skew-adjoint endomorphisms for the indicated Lorentz metric."),
            Definition("coordinates", "lorentzCoords", "Rotation and boost coordinates",
                "The rotation coordinates are (−X₂₃,−X₃₁,−X₁₂) and the boost coordinates are (X₀₁,X₀₂,X₀₃). "
                + "The skew-adjoint equation forces every diagonal entry to vanish, every time-space pair to agree and every spatial pair to have opposite signs. "
                + "The inverse puts the rotation and boost coordinates into precisely those entries. Both maps are linear."),
            Definition("cross", "cross", "Oriented cross product",
                "For triples a and b, the entries are a₁b₂−a₂b₁, a₂b₀−a₀b₂ and a₀b₁−a₁b₀ in zero-based indices."),
            Result("lorentz-bracket", "lorentz_coords_bracket", "Lorentz bracket in six coordinates",
                "For rotation and boost triples (a,b) and (c,d), ordinary matrix commutation has coordinates "
                + "(a×c−b×d, a×d+b×c). Multiplication of the explicit four-by-four matrices proves each component."),
            Result("real-dimension", "finrank_lorentz_real", "Real dimension six",
                "The coordinate linear equivalence identifies the real carrier with a product of two three-dimensional spaces."),
            Definition("sl-two", "SL2C", "Complex special linear Lie algebra",
                "The special linear carrier consists of traceless complex two-by-two matrices."),
            Definition("pauli", "pauli", "Normalized Pauli map",
                "The image of z has diagonal entries −iz₂/2 and iz₂/2 and off-diagonal entries "
                + "(−iz₀−z₁)/2 and (−iz₀+z₁)/2."),
            Definition("pauli-coordinates", "pauliCoords", "Pauli linear equivalence",
                "For a traceless matrix M, the inverse triple is (i(M₀₁+M₁₀), M₁₀−M₀₁, 2iM₀₀). "
                + "The trace condition recovers the remaining diagonal entry and i²=−1 proves both compositions."),
            Result("pauli-bracket", "pauli_bracket", "The Pauli commutator",
                "The commutator of the Pauli images of two triples is the Pauli image of their cross product. "
                + "Expanding the four entries and reducing i²=−1 proves the identity."),
            Definition("real-equivalence", "lorentz_real_sl2", "Real Lie equivalence",
                "The real-linear map takes (a,b) to the Pauli image of a−ib in the real restriction of scalars of the complex special linear algebra. "
                + "The coordinate inverse uses real part and negative imaginary part. The Lorentz bracket becomes the Pauli commutator because the complex cross product of a−ib and c−id equals (a×c−b×d)−i(a×d+b×c)."),
            Definition("complex-factors", "lorentz_chiral_sl2_prod", "Two complex Lie factors",
                "Send (a,b) to the two Pauli images of a−ib and a+ib. For their coordinate triples u and v the inverse is "
                + "a=(u+v)/2 and b=−i(v−u)/2. Expanding both cross products verifies preservation of the Lie bracket."),
            Definition("complexification", "lorentz_base_change", "Complexification of real matrices",
                "Tensor extension over the real numbers gives the complex matrix algebra. A pure tensor z⊗X has coordinates z times the real coordinates of X. "
                + "The tensor equivalences distributing over the coordinate product and its three scalar entries supply the linear inverse. "
                + "The coordinate bracket table proves compatibility on pure tensors, and additivity extends it to all tensors."),
            Definition("complexified-product", "complexified_chiral_sl2_prod", "Complexified chiral Lie equivalence",
                "Composing the extension-of-scalars equivalence with the two-factor Pauli equivalence identifies the complexification with the product of two complex special linear Lie algebras."),
            Definition("rotation-generator", "J", "Rotation generators",
                "The rotation generator has its coordinate unit vector in the rotation triple and zero boost triple."),
            Definition("boost-generator", "K", "Boost generators",
                "The boost generator has zero rotation triple and its coordinate unit vector in the boost triple."),
            Definition("positive-chiral", "chiralPlus", "First chiral generator",
                "The first combination of the generators is (J+iK)/2."),
            Definition("negative-chiral", "chiralMinus", "Second chiral generator",
                "The second combination of the generators is (J−iK)/2."),
            Result("generator-images", "chiral_generator_images", "Images of the chiral generators",
                "Each first chiral generator maps to its Pauli basis element in the first factor and zero in the second. "
                + "Each second chiral generator gives zero in the first factor and its Pauli basis element in the second."),
            Result("mixed-bracket", "chiral_mixed_bracket", "Mixed brackets vanish",
                "First and second chiral generators lie in different factors. Their product-Lie commutator vanishes componentwise and the Lie equivalence is injective."),
            Result("chiral-brackets", "chiral_brackets", "The chiral commutator table",
                "Within either factor, the commutator is the Pauli image of the cross product of the two coordinate unit vectors. "
                + "These cross products give the oriented antisymmetric structure constants. The mixed commutator is zero."),
            Result("hodge-blocks", "lorentz_hodge_blocks", "Lorentzian Hodge operator",
                "The second exterior power of the metric is diagonal with minus one in the electric block and plus one in the magnetic block. "
                + "It is its own inverse. The Urbantke wedge pairing exchanges the two blocks, so the volume-one Hodge matrix takes (E,B) to (B,−E).", true),
            Result("hodge-square", "real_hodge_square", "Real Hodge square",
                "Applying the signed block matrix twice negates each two-form coefficient.", true),
            Definition("two-form", "lorentz_to_twoForm", "The covariant two-form",
                "Multiply the Lorentz endomorphism by the metric on the left and extract entries in the oriented pair order."),
            Result("two-form-coordinates", "twoForm_coords", "Two-form coordinates of the Lorentz generator",
                "The lowered time-space entries are the negatives of the boost coordinates. The cyclic spatial entries are the negatives of the rotation coordinates. "
                + "The resulting pair is (−b,−a)."),
            Result("chiral-eigenspaces", "hodge_eigenspaces_eq_chiral", "Hodge eigenspaces and the two Lie factors",
                "Under index lowering, a Lorentz matrix has Hodge eigenvalue −i exactly when its second Pauli factor vanishes. "
                + "Eigenvalue +i similarly characterizes vanishing of the first factor. The electric block equation determines the rotation triple in terms of the boost triple, and the magnetic equation follows from i²=−1.", true),
            Definition("graph", "chiralGraph", "Three-column chiral graph",
                "The electric block is the identity matrix and the magnetic block is z times the identity."),
            Result("graph-eigen", "hodge_eigen_graph", "Graph of a Hodge eigenvalue",
                "For z²=−1 a vector is a z eigenvector exactly when its magnetic triple is z times its electric triple. "
                + "Each electric triple determines one such vector and the second block equation follows from z²=−1."),
            Result("graph-gram", "chiral_graph_gram", "Wedge Gram matrix of the graph",
                "The two complementary blocks each contribute z times the identity to the wedge Gram matrix, yielding 2z times the identity.", true),
            Result("graph-conjugation", "chiral_graph_conj", "Conjugation exchanges the graphs",
                "Entrywise conjugation fixes the identity electric block and takes i to −i in the magnetic block."),
            Result("urbantke-normalization", "urbantke_chiral_graph", "Urbantke Lorentzian normalization",
                "For the graph with magnetic block iI, the frozen cubic metric is minus the chosen Lorentz metric and its volume coefficient is −i. "
                + "This is the graph carrying eigenvalue +i of the real volume-one Hodge matrix.", true),
            Definition("screen-wedge", "screenWedge", "Bivector of the null screen",
                "The raw wedge entries use the complex screen vector followed by the real null generator in the oriented pair order."),
            Result("screen-chirality", "weyl_screen_in_chiral_plane", "Null screen bivector in a Hodge plane",
                "In both stereographic charts the raw magnetic triple is −i times the electric triple. "
                + "The signed Hodge matrix thus has eigenvalue −i on the screen wedge. Lowering two contravariant indices reverses the electric signs and exchanges the graph.", true)),
        []));

    private static DocumentBlock Definition(string id, string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static DocumentBlock Result(string id, string name, string title, string prose, bool sources = false) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(),
            sources ? AssessedProvenance.FromRepo(Jacobson, Urbantke) : AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
