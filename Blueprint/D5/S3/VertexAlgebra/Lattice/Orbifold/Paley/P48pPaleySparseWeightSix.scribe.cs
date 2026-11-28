using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.Orbifold.Paley;

internal sealed class P48pPaleySparseWeightSixDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/Orbifold/Paley/P48pPaleySparseWeightSix.";
    private static readonly LibraryNoteRef ConwaySloane =
        LibraryNoteRef.Create("D5/L/Geometry/conwaysloane1999spherepackings");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The ternary Paley certificate excludes squared norm four in the odd neighbor of the catalogue lattice P48p.",
        H("The P48p Paley Norm-Four Certificate"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("p48p-paley-norm-ne-four"),
                DeclarationHandle.Create(Prefix + "norm_ne_four"),
                H("The catalogue odd neighbor has no vector of squared norm four"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(ConwaySloane),
                Blocks(
                    Paragraph(Text("In the catalogue basis, take the integral rows pairing evenly with the first "
                        + "frame vector and adjoin half of that frame vector. The theorem excludes squared norm "
                        + "four for every row in this odd neighbor, using the rational extension of the catalogue "
                        + "Gram form. Conway and Sloane’s Sphere Packings, Lattices and Groups provides lattice "
                        + "background. The Gram matrix and the group generators used to build the frame come "
                        + "from the GRAM and GROUP_GENERATORS sections of the Nebe–Sloane P48p entry "
                        + "(https://www.math.rwth-aachen.de/~Gabriele.Nebe/LATTICES/P48p.html).")),
                    Paragraph(Text("A vector of squared norm four would have integral half-frame pairings with "
                        + "square sum twelve. Their residue modulo three is nonzero, since an all-zero residue "
                        + "would make the square sum divisible by nine. It has Hamming weight at most twelve "
                        + "and lies in the ternary syndrome kernel. Its two signed chart halves form a Paley "
                        + "graph pair. Since the Paley matrix squares to the identity over the ternary field, "
                        + "the lighter half can be taken as a nonzero input of weight at most six. The checked "
                        + "small-support bound forces the two weights to sum to more than twelve.")),
                    Paragraph(Text("The existence of an extremal vertex operator algebra of central charge 48 "
                        + "remains an open problem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("p48p-paley-anchored-weight-six"),
                DeclarationHandle.Create(Prefix + "anchored_weight_six_sparse"),
                H("Every anchored weight-six input has total weight above twelve"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The weight-preserving projective action sends three occupied directions "
                        + "to infinity, zero and one. An overall sign sets the coefficient at infinity to one. "
                        + "The two other anchors have four sign pairs. Choose three distinct slopes from the "
                        + "remaining 21 and give each one of two signs. This gives 4 × 1330 × 8 = 42,560 "
                        + "anchored inputs, where 1330 is the number of three-element subsets of 21 slopes.")),
                    Paragraph(Text("The kernel checks the branches by anchor sign pair, first chosen slope and "
                        + "its sign. For each input, the checker sums the six character contributions in each "
                        + "output coordinate modulo three and stops at the seventh nonzero coordinate. The "
                        + "soundness proof relates those sums to multiplication by the Paley matrix, yielding "
                        + "output weight at least seven. The input has weight six, so the total exceeds twelve. "
                        + "The checks for weights one through five complete the small-support bound."))),
                DescribeRole.Theorem))));
}
