using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.Orbifold;

internal sealed class P48qInvariantQuadraticsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/Orbifold/P48qInvariantQuadratics.";
    private static readonly LibraryNoteRef Nebe =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/nebe2014extremal48");
    private static readonly LibraryNoteRef BakalovKac =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The quadratic states of complementary invariant Cartan blocks give two linearly independent fixed vectors in weight two of the untwisted P48q lattice carrier.",
        H("Fixed Weight-Two States in the Untwisted P48q Lattice"),
        Blocks(
            Paragraph(Text("Let D be lattice data whose real Gram matrix is positive definite, and write B for the rational extension of its Gram pairing. "
                + "For a rational Cartan subspace W, choose a basis of W and its dual for the restricted Gram form. "
                + "The quadratic state of W is one half of the sum of the minus-one mode products of the corresponding pairs of currents. "
                + "This is the block version of the inverse-form quadratic construction in Bakalov–Kac, Section 4.1, equation (4.16) of arXiv:math/0402315v1.")),
            Describe.Lean(
                DescribeId.Create("quadratic-mode-one-on-block"),
                DeclarationHandle.Create(Prefix + "blockQuadratic_mode_one_of_mem"),
                H("Mode one fixes the currents in the block"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(BakalovKac),
                Blocks(Paragraph(Text("For every direction x in W, mode one of its block quadratic acts as the identity on the current of x. "
                    + "The two contractions of the quadratic with that current reconstruct x from its basis and dual basis coordinates. "
                    + "The factor of one half cancels the two copies."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("quadratic-mode-one-on-orthogonal"),
                DeclarationHandle.Create(Prefix + "blockQuadratic_mode_one_of_orthogonal"),
                H("Mode one kills the perpendicular currents"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(BakalovKac),
                Blocks(Paragraph(Text("For every rational direction perpendicular to W, mode one of the quadratic state of W sends its current to zero. "
                    + "All contractions vanish because the basis and dual basis vectors lie in W."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("invariant-block-quadratics"),
                DeclarationHandle.Create(Prefix + "invariant_block_quadratics"),
                H("Independent fixed quadratics from invariant blocks"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(BakalovKac),
                Blocks(
                    Paragraph(Text("Let a group act on the rational Cartan space preserving B. Let its complex representation on the lattice carrier "
                        + "intertwine the rational currents and preserve all mode products. For every nonzero proper invariant subspace W, "
                        + "the quadratic states of W and its B-orthogonal complement have weight two, are fixed by the group, and are linearly independent over ℂ.")),
                    Paragraph(Text("The orthogonal complement is invariant because the Cartan action preserves B. Each action transports a basis and its Gram-dual basis together, "
                        + "and the quadratic sum is basis independent. The minus-one product of two weight-one currents has weight two. "
                        + "Mode one on a nonzero current from each block distinguishes the two states."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-to-three-fixed-weight-two"),
                DeclarationHandle.Create(Prefix + "p48q_prime_to_three_fixed_weight_two"),
                H("Two fixed weight-two states for P48q"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Nebe, BakalovKac),
                Blocks(Paragraph(Text("Let H ≤ SL₂(F₄₇) have order prime to three and act faithfully on the rational P48q Cartan space preserving its Gram form. "
                    + "Suppose its complex representation on the untwisted lattice carrier intertwines the rational currents and preserves all mode products. "
                    + "There are two complex-linearly independent states of weight two fixed by every element of H. "
                    + "The rank-48 rational reducibility theorem supplies the nonzero proper invariant block, and the certified positive definite Gram matrix gives its complementary block."))),
                DescribeRole.Theorem))));
}
