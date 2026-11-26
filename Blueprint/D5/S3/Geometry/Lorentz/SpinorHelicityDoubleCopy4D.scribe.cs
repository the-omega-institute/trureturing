using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Lorentz;

internal sealed class SpinorHelicityDoubleCopy4DDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D.";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/LieTheory/benincasacachazo2007smatrix");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complex spinor factorizations and momentum conservation give the four-particle consistency laws and the four-point tree double copy.",
        H("Four-dimensional spinor helicity and the tree double copy"),
        Blocks(
            Paragraph(Text("Write the null momentum as the outer product of two independent complex spinors, "
                + "and use the negative two-by-two determinant for the Mandelstam invariant. "
                + "Real null rays use conjugate spinors in the stereographic chart.")),
            Result("bracket-antisymmetry", "bracket_antisymm", "Antisymmetry of the spinor bracket",
                "Swapping the two spinors exchanges the two terms of their determinant."),
            Result("bracket-self", "bracket_self", "A spinor brackets to zero with itself",
                "The two scalar products in the bracket coincide by commutativity."),
            Result("bracket-dependence", "bracket_zero_iff_dependent", "Vanishing bracket and dependence",
                "The bracket of u and v vanishes exactly when u is zero or v is a scalar multiple of u. "
                + "A nonzero coordinate of u determines that scalar, and the determinant equation gives the remaining coordinate."),
            Result("spinor-null", "spinor_det_null", "A spinor outer product is null",
                "The determinant of the two-by-two outer product vanishes by direct expansion."),
            Result("null-rank-one", "null_iff_rankOne", "Null momenta admit spinor factors",
                "A matrix has zero determinant exactly when it is an outer product. A nonzero first column "
                + "determines one factor and a nonzero entry of that column normalizes the other. "
                + "If the first column vanishes, the second column alone gives the factorization."),
            Result("schouten", "schouten", "Schouten identity",
                "For spinors a, b, c and d, the sum of the products of brackets in pairings (ab)(cd), "
                + "(ac)(db) and (ad)(bc) vanishes by expansion."),
            Result("mandelstam-brackets", "mandelstam_brackets", "Mandelstam invariants from brackets",
                "The negative determinant of two summed null momenta equals their left bracket times their reversed right bracket."),
            Result("det-sigma", "det_sigma", "Minkowski norm from the spinor matrix",
                "The negative determinant of the Hermitian matrix with diagonal entries x₀ ± x₃ "
                + "and off-diagonal entries x₁ ∓ ix₂ is the Minkowski square in signature (−+++)."),
            Result("north-chart", "nullGenerator_spinor_factor", "Spinor factors of the finite-chart generator",
                "At z the Hermitian momentum matrix is twice the outer product of (1,z) with (1,conjugate z)."),
            Result("south-pole", "nullGenerator_south_factor", "Spinor factors at the south pole",
                "At infinity the Hermitian momentum matrix is twice the outer product of (0,1) with itself."),
            Result("three-point-branches", "three_point_branches", "Three-point momentum conservation has two branches",
                "If all left brackets vanish there is a left branch. If some left pair is independent, "
                + "its two contractions with conservation express both corresponding right spinors "
                + "as multiples of the remaining right spinor. All right brackets then vanish, including in degenerate configurations."),
            Result("bcfw-clearing", "bcfw_iff_cleared", "Clearing the two shifted amplitudes",
                "For nonzero x, y, x+y and nonzero prefactors P and K, equality of the two rational shifts "
                + "is equivalent to zero of the channel polynomial. Their difference is that polynomial "
                + "times P K^(s−1) divided by x^(s−1) y^(s−1) (x+y).", literature: true),
            Result("channel-chart", "generic_channel_chart", "Conserved channel coordinates",
                "An explicit four-spinor chart realizes x, y and x+y as the three bracket products. "
                + "Whenever x+y is nonzero, the spinor prefactor K is nonzero."),
            Result("spin-one", "spin_one_consistency_iff_jacobi", "Spin-one shift consistency is Jacobi",
                "For alternating couplings the channel polynomial factors as −(x+y) times the component Jacobi sum. "
                + "Evaluating at x=y=1 recovers Jacobi, and the factorization gives the converse at each generic pair.", literature: true),
            Result("spin-two", "spin_two_consistency_iff_associative", "Spin-two shift consistency is associativity",
                "For symmetric couplings the channel polynomial factors as (x+y)(y(U−V)−x(W−V)). "
                + "The equation at x=y=1 gives W=U, the associativity equation on basis components. "
                + "Permuting the species gives V=U, which makes both terms vanish throughout the chart.", literature: true),
            Result("higher-spin", "higher_spin_single_zero", "A single species of spin at least three has zero coupling",
                "At x=y=1 the shift equation identifies the crossed and uncrossed contractions. "
                + "At x=1 and y=2 the equation becomes (2^(s−1)−2)g²=0. "
                + "The coefficient is strictly positive for every integer s at least three.", literature: true),
            Result("spin-two-split", "spin_two_orthogonal_split", "Orthogonal one-dimensional spin-two sectors",
                "On a finite-dimensional real inner-product space, associative and commutative multiplication gives commuting "
                + "multiplication maps. Symmetry makes them jointly orthogonally diagonalizable. In a common orthonormal basis, "
                + "a product of distinct vectors lies in both corresponding lines, hence vanishes. Every basis vector's square lies in its own line."),
            Result("complementary-mandelstam", "mandelstam_complement", "Complementary momentum channels agree",
                "Conservation identifies each pair sum with minus its complement. Their two-by-two determinants agree."),
            Result("mixed-matter", "nonzero_graviton_matter_universal", "Mixed four-point consistency forces equal couplings",
                "Conservation gives s+t+u=0 and turns the ratio of the two dotted bracket products into t/s. "
                + "This reduces the two shifts to expressions differing by the common nonzero spinor factor times κa(κ−κa)/s. "
                + "A nonzero matter coupling therefore equals the graviton coupling. The Laurent exponents are algebraic. "
                + "The scattering interpretation requires constructibility and the stated mixed vertices.", literature: true),
            Result("soft-ward", "soft_ward_universal", "Soft gauge invariance forces equal couplings",
                "The leading soft polarization variation cancels each nonzero soft denominator. "
                + "Conservation reduces the resulting equation to the coupling difference times the total matter momentum tested by any covector. "
                + "The dual separates points, so nonzero total matter momentum forces equality."),
            Result("gravity-bcfw", "gravityMHV4_bcfw", "The gravity amplitude from the spin-two shift",
                "Schouten gives z=x+y for the permuted helicity labels, so the shift factor 1−y/z is x/z. "
                + "Substitution into the independent spin-two shift value gives the rational gravity amplitude."),
            Result("klt-four-point", "klt_four_point", "Exact four-point KLT relation",
                "For conserved four-spinor momenta with nonzero angle brackets, minus the Mandelstam invariant "
                + "of the first pair times the two Parke–Taylor amplitudes in orders 1234 and 1243 equals the stripped MHV graviton amplitude. "
                + "Antisymmetry and the complementary-channel identity align the numerators after clearing denominators.")),
        []));

    private static DocumentBlock Result(string id, string name, string title, string prose, bool literature = false) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
