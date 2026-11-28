using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Gauge;

internal sealed class E6TrinificationUnification4DDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Gauge/E6TrinificationUnification4D.";
    private static readonly LibraryNoteRef Slansky =
        LibraryNoteRef.Create("D5/L/LieTheory/slansky1981unifiedgroups");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exceptional root system, chiral weight traces, and invariant matrix cubic.",
        H("Exceptional roots and trinification"),
        Blocks(
            Paragraph(Text("The root coordinates use an integral code scaled by one half. The chiral basis combines the even half-spin weights, the fundamental vector weights and their duals, and a neutral state. Right indices zero, one, and two label the up antiquark, down antiquark, and exotic antiquark in the conjugate quark block. Those indices label the up doublet, down doublet, and lepton doublet in the corresponding columns of the lepton block.")),
            Entry("state-card", "state_card", "Chiral multiplet dimension",
                "The chiral state type has sixteen spinor states, two sets of five vector states, and one singlet, for a total of twenty-seven. Every state has psi charge one, minus two, or four.", Slansky),
            Entry("spinor-sm-bridge", "spinor_sm_bridge", "One Standard Model family and a neutral state",
                "The spinor block contains the fifteen Standard Model weights, compared with the preceding gauge unification module, and one hypercharge and isospin neutral state.", Slansky),
            Entry("spinor-occupation-bridge", "spinor_occupation_bridge", "Spinor charges from occupation coordinates",
                "The half-spin occupation coordinates recover the hypercharge, isospin, electric charge, and baryon-minus-lepton charge of each spinor state."),
            Entry("linear-traces", "linear_traces", "Vanishing linear traces",
                "Hypercharge, weak isospin, electric charge, the two extra abelian charges, and baryon-minus-lepton charge each have sum zero over the twenty-seven states."),
            Entry("trace-pairing", "trace_pairing", "Complete quadratic trace pairing",
                "The trace of the product of arbitrary linear combinations of hypercharge, weak isospin, and the two additional charges is the diagonal bilinear form with coefficients five, three, seventy-two, and one hundred twenty."),
            Entry("pairwise-orthogonality", "pairwise_orthogonality", "Orthogonal diagonal generators",
                "All six mixed traces between hypercharge, weak isospin, and the two extra abelian charges vanish."),
            Entry("quadratic-traces", "quadratic_traces", "Exact quadratic indices",
                "The weak-isospin, hypercharge, electric-charge, psi-charge, and chi-charge square sums are respectively three, five, eight, seventy-two, and one hundred twenty."),
            Entry("weinberg-trace-ratio", "weinberg_trace_ratio", "Tree-level weak mixing ratio",
                "The ratio of the weak-isospin square trace to the electric-charge square trace is three eighths."),
            Entry("universal-abelian-cubic", "universal_abelian_cubic", "Cubic anomaly polynomial",
                "The sum of cubes of any real linear combination of hypercharge, weak isospin, psi charge, and chi charge vanishes."),
            Entry("mixed-abelian-cubic", "mixed_abelian_cubic", "Mixed cubic traces",
                "The sum of the pointwise product of three independently chosen real linear combinations of the four generators vanishes."),
            Entry("color-content", "color_content", "Color multiplet counts",
                "The chiral basis has nine triplet components, nine antitriplet components, and nine singlets. The colored components form three triplet and three antitriplet multiplets."),
            Entry("color-anomalies", "color_anomalies", "Pure color and mixed color anomalies",
                "The signed cubic color trace vanishes. The color-index-weighted sum of any real linear combination of the four abelian weights also vanishes."),
            Entry("trinification-weights", "trinification_weights", "Electric and electroweak weight identification",
                "The explicit coordinate equivalence preserves hypercharge, weak isospin, and electric charge state by state."),
            Entry("trinification-extra-charges", "trinification_extra_charges", "Additional trinification charges",
                "The coordinate equivalence preserves the psi and chi charges and their baryon-minus-lepton combination with hypercharge."),
            Entry("trinification-color", "trinification_color", "Color-preserving coordinate equivalence",
                "The equivalence preserves each state’s color sector and its color index when the state has one."),
            Entry("e6roots-card", "e6Roots_card", "Seventy-two exceptional roots",
                "The integral sign-code construction gives forty integral roots and thirty-two half-integral roots, and its realization is injective."),
            Entry("e6roots-in-rank6-subspace", "e6Roots_in_rank6_subspace", "Exceptional root subspace",
                "The sixth and seventh coordinates agree and are negatives of the eighth. The subspace of vectors with these two constraints has dimension six."),
            Entry("e6-lie-algebra-dimension", "e6_lie_algebra_dimension", "Root-space dimension count",
                "The six Cartan dimensions and the seventy-two root positions give a count of seventy-eight."),
            Entry("e6roots-simply-laced", "e6Roots_simply_laced", "Common squared root length",
                "Every vector in the exceptional root set has squared Euclidean length two."),
            Entry("e6roots-crystallographic-inner-products", "e6Roots_crystallographic_inner_products", "Integral root pairings",
                "Two roots have inner product in the five integers from minus two through two. The extreme values distinguish opposite and equal roots, respectively."),
            Entry("e6roots-weyl-reflection-closed", "e6Roots_weyl_reflection_closed", "Weyl reflection and negation",
                "Subtracting the inner product times the reflecting root from a second root gives another root. Negating a root gives a root as well."),
            Entry("e6-dynkin-simple-roots", "e6_dynkin_simple_roots", "Exceptional simple system and Cartan determinant",
                "Six displayed roots are linearly independent and give the Bourbaki Cartan matrix of determinant three. Each root expands in their basis with integral coefficients of one weak sign."),
            Entry("e6-root-span", "e6_root_span", "Full rank of the root span",
                "The root span equals the six-dimensional subspace described by the two coordinate equations."),
            Entry("trinification-diagonal-generators", "trinification_diagonal_generators", "Trace-free electroweak diagonals",
                "The left and right hypercharge diagonals and weak-isospin diagonal have zero trace. Subtracting the isospin diagonal from the left hypercharge diagonal gives the right hypercharge diagonal."),
            Entry("trinif-dimension", "trinif_dimension", "Matrix-space dimension",
                "The three complex three by three matrix blocks have total complex dimension twenty-seven. Two triples coincide exactly when their entries agree at every index of the chiral basis."),
            Entry("trinif-cyclic-equivariance", "trinif_cyclic_equivariance", "Cyclic symmetry of the group action",
                "Cycling the three matrices intertwines the rotation of the three determinant-one factors. Three rotations act as the identity."),
            Entry("trinif-action-kernel", "trinif_action_kernel", "Diagonal cube-root kernel",
                "A group element acts trivially on all three matrices exactly when its three factors are the same scalar matrix and that scalar has cube one."),
            Entry("trinif-cartan-cubic-anomaly", "trinif_cartan_cubic_anomaly", "Arbitrary trinification Cartan anomaly",
                "For any three trace-free diagonals, the sum of cubes of the cyclic differences over all matrix entries vanishes."),
            Entry("freudenthalcubic-sl3-cubed-invariant", "freudenthalCubic_sl3_cubed_invariant", "Determinant-one change of bases",
                "The three determinants and the trace of the triple product give an invariant of determinant-one changes of basis on the three matrix spaces."),
            Entry("freudenthalcubic-z3-cyclic-invariant", "freudenthalCubic_z3_cyclic_invariant", "Cyclic invariance of the cubic",
                "Cyclic permutation of the three matrix arguments preserves the sum of determinants minus the trace of their product."),
            Entry("freudenthalcubic-homogeneous-degree-3", "freudenthalCubic_homogeneous_degree_3", "Degree-three homogeneity",
                "Scaling all three matrices by a complex scalar multiplies the invariant by the cube of the scalar."),
            Entry("trinif-cubic-stabilizer", "trinif_cubic_stabilizer", "Cubic-preserving linear action and cyclic element",
                "The determinant-one factors act by linear automorphisms in the cubic stabilizer. The cyclic element has exact order three and conjugates the action by rotation of the three factors."),
            Entry("freudenthalcubic-contains-sm-yukawa", "freudenthalCubic_contains_sm_yukawa", "Quark and lepton Yukawa coefficients",
                "The two weak rows in the trace terms at right indices zero and one supply the up and down quark couplings. The determinant uses the three distinct right indices and the alternating contraction of the two weak rows. Its expansions at the charged and neutral singlets give the charged-lepton and Dirac-neutrino couplings."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement,
        params LibraryNoteRef[] acknowledgements) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(acknowledgements),
            Blocks(Paragraph(Text(statement))), DescribeRole.Theorem);
}
