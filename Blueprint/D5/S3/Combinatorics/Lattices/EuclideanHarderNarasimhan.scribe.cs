using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Lattices;

internal sealed class EuclideanHarderNarasimhanDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/grayson1984semistability");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gram covolumes and Euclidean Harder-Narasimhan filtrations",
        H("Basis invariance and saturated sublattices"),
        Blocks(
            Paragraph(Text("Let E be a real inner product space and M an integral "
                + "submodule which is finite and free over the integers. Choose an "
                + "integral basis and define the covolume to be the nonnegative square "
                + "root of its Gram determinant. No full-rank assumption is imposed.")),
            Describe.Lean(DescribeId.Create("integral-basis-gram-volume"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Lattices/EuclideanHarderNarasimhan.covolume_eq_gram"),
                H("Every integral basis computes the covolume"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For every finite indexing type and every integral "
                        + "basis b of M, the covolume equals the square root of the "
                        + "determinant of the matrix with entries inner(b(i),b(j)). "
                        + "Changing the basis multiplies this matrix on the left by "
                        + "the transpose of the integer change matrix and on the right "
                        + "by the change matrix. Its determinant is a unit in the "
                        + "integers, hence equals one or minus one. Its square is one, "
                        + "so the Gram determinant is unchanged.")),
                    Paragraph(Text("Different finite indexing types are identified by "
                        + "the basis index equivalence. Simultaneous row and column "
                        + "reindexing preserves the determinant. In rank zero the "
                        + "empty Gram matrix has determinant one and covolume one. "
                        + "The identity also holds for finite free integral submodules "
                        + "whose images are linearly dependent over the reals; their "
                        + "Gram determinant and covolume vanish. For a discrete "
                        + "submodule the integral basis is real-linearly independent "
                        + "in its real span, so its covolume is positive."))),
                DescribeRole.Theorem),
            Describe.Remark(DescribeId.Create("classical-euclidean-hn"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Lattices/EuclideanHarderNarasimhan.euclidean_hn"),
                H("The classical Euclidean lattice filtration"),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The canonical filtration of a Euclidean lattice "
                    + "by saturated sublattices with semistable factors and strictly "
                    + "decreasing slopes is classical: Stuhler's reduction theory and "
                    + "Grayson's canonical semistability filtration are the literature "
                    + "sources. The Library note locates these conclusions. The concrete "
                    + "Gram proof, arbitrary-interval formulation, exact index factor "
                    + "and conjunction of endpoint identities below are repo-derived; "
                    + "they are not asserted to be verbatim statements of those papers.")))),
            Describe.Lean(DescribeId.Create("covolume-exact-index"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Lattices/EuclideanHarderNarasimhan.covolume_index"),
                H("Exact index and equality of covolumes"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Let M and N be integral submodules of a finite-dimensional "
                    + "real inner product space, with M contained in N, N discrete, "
                    + "and equal real spans. The smaller submodule is discrete by "
                    + "inclusion. The relative additive index n of M in N is positive; "
                    + "covolume(M) equals n times covolume(N). Their covolumes are equal "
                    + "exactly when M equals N. In particular, this applies to the "
                    + "ordinary sum of two saturated sublattices and their saturated "
                    + "join. The determinant "
                    + "of the integral inclusion matrix has absolute value n. This uses "
                    + "the pinned AddSubgroup.relIndex_eq_natAbs_det, including rank zero; "
                    + "no full-rank assumption in the ambient space is needed."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("euclidean-covolume-hn"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Lattices/EuclideanHarderNarasimhan.euclidean_hn"),
                H("Covolume inequality and the Euclidean HN filtration"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Let E be a finite-dimensional real inner product space "
                        + "and let L be a discrete integral submodule. A saturated "
                        + "sublattice consists of all points of L in its real span. "
                        + "The meet is intersection; the join is the saturation in L "
                        + "of the sum. Write U and V for their integral carriers, "
                        + "S for U plus V, and J for the integral carrier of the join. "
                        + "With n the positive index of S in J, n times the covolumes "
                        + "of the meet and J is at most covolume(U) times covolume(V). "
                        + "Both factors on the right use the same covolume definition.")),
                    Paragraph(Text("The common intersection is primitive in A and B. "
                        + "Its integral basis extends to both, and the combined "
                        + "extensions form an integral basis of the sum. The overlapping "
                        + "Gram volume inequality bounds the covolume of that sum. "
                        + "It holds even in a seminormed inner product space: if the "
                        + "common Gram block has zero determinant, the other principal "
                        + "minors are nonnegative. If its determinant is nonzero, that "
                        + "block is positive definite; Schur elimination and Fischer's "
                        + "inequality for the residual positive semidefinite matrix "
                        + "give the bound after multiplication by the common determinant "
                        + "squared. Linear independence is not the branch criterion. "
                        + "The sum has covolume exactly n times the covolume of its "
                        + "saturation J. Equality of these two covolumes holds exactly "
                        + "when the sum is already saturated.")),
                    Paragraph(Text("Define the degree of a saturated sublattice as "
                        + "minus the logarithm of its positive covolume. The volume "
                        + "inequality makes this degree supermodular, and integral "
                        + "rank is strict and modular. Saturated carriers form the "
                        + "closed-element lattice of real-span saturation. The integer "
                        + "rank equals real-span dimension by ZLattice.rank; saturation "
                        + "preserves it, strict inclusion of closed carriers strictly "
                        + "increases it, and the submodule rank identity gives the "
                        + "modular law. A unique HN endpoint list "
                        + "between A and B exists exactly when A is contained in B. "
                        + "Its factors are nonzero semistable intervals and its "
                        + "successive slopes strictly decrease.")),
                    Paragraph(Text("For a nonempty filtration with first endpoint e "
                        + "and last lower endpoint q, A is contained in q and q is "
                        + "properly contained in B. The first slope is the attained "
                        + "greatest slope of all nonzero subobjects of the interval; "
                        + "the last slope is the attained least slope of all nonzero "
                        + "quotients. They equal the defined maximal and minimal slopes. "
                        + "The first endpoint is the largest destabilizer. Semistability "
                        + "is equivalent both to having one factor and to equality "
                        + "of the two extreme slopes. Otherwise the first slope is "
                        + "strictly larger than the last.")),
                    Paragraph(Text("No covolume inequality or equivalent geometric "
                        + "comparison is assumed. Rank-zero sublattices have covolume "
                        + "one. The statement does not impose full rank on L in E "
                        + "and does not include a slope bound for linear maps."))),
                DescribeRole.Theorem))));
}
