using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.ProbabilityTransport;

internal sealed class WeightedProjectionMinorsHermitianDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/ProbabilityTransport/WeightedProjectionMinorsHermitian.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Geometry/mazhang2026weightedminors");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Over the reals and the complex numbers, pair and triple minors have equal total mass, every "
            + "pair family is dominated by its triple neighbourhood, and signed weights obey min and max bounds.",
        H("Signed, complex and two-sided weighted-minor comparison"),
        Blocks(
            Describe.Lean(DescribeId.Create("weighted-minors-hermitian-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Mass identity, pair-family domination and two-sided weighted bounds"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "Let 𝕜 be ℝ or ℂ, n any natural number, and x, y, z vectors in the Euclidean space 𝕜^n "
                        + "with ‖z‖ = 1 and ⟪z, x⟫ = ⟪z, y⟫ = 0; x and y need not be unit or orthogonal, and "
                        + "may be zero or dependent. Put p_ij = x_i y_j − x_j y_i and let q_ijk be the "
                        + "determinant with rows x, y, z and columns i, j, k; sums run over increasing indices. "
                        + "Then Σ_{i<j} |p_ij|² = Σ_{i<j<k} |q_ijk|². For every symmetric relation F on the "
                        + "indices, Σ_{i<j, F(i,j)} |p_ij|² ≤ Σ |q_ijk|² over the increasing triples having "
                        + "at least one pair in F. For every real symmetric weight array a, "
                        + "Σ_{i<j<k} min(a_ij, a_ik, a_jk)|q_ijk|² ≤ Σ_{i<j} a_ij |p_ij|² ≤ "
                        + "Σ_{i<j<k} max(a_ij, a_ik, a_jk)|q_ijk|².")),
                    Paragraph(Text(
                        "The triple array is the lift z ∧ p, the alternating array z_i p_jk − z_j p_ik + z_k p_ij. "
                        + "Its adjoint is the contraction b ↦ Σ_k conj(z_k) b_kij, and summing over ordered "
                        + "tuples gives the energy identity Σ|lift v|² + 6Σ|contract v|² = 3‖z‖²Σ|v|² for "
                        + "every skew array v. For v = p the contraction vanishes by the orthogonality "
                        + "hypotheses, giving the mass identity. For an alternating array b, Cauchy–Schwarz "
                        + "applied to the adjoint pairing bounds the pair mass of its contraction by its "
                        + "triple mass. Contracting q gives back p, and at a pair of F the contraction only "
                        + "uses triples meeting F, which proves the family domination. Nonnegative weights "
                        + "are expanded over their upper level sets, which are symmetric pair families whose "
                        + "triple neighbourhoods are the upper level sets of the triple maxima. Arbitrary "
                        + "weights are shifted by a constant, and the shift cancels on both sides by the mass "
                        + "identity. Negating the weights gives the lower bound. Ordered sums are reduced to "
                        + "increasing indices by symmetry. This is Theorem 1, Lemma 2 and Corollaries 3 and 4 "
                        + "of H. Ma and W. Zhang (DOI 10.5281/zenodo.23931738), on the question of meler in "
                        + "MathOverflow 469781, extending the orthonormal comparison of Lyons and the "
                        + "two-sided complex comparison of Miller and Bistroń."))),
                DescribeRole.Theorem))));
}
