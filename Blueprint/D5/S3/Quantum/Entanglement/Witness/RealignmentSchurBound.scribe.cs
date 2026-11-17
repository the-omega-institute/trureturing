using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.Witness;

internal sealed class RealignmentSchurBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/Witness/RealignmentSchurBound.";
    private static readonly LibraryNoteRef Lps =
        LibraryNoteRef.Create("D5/L/Entropy/lipoonsze2011realignment");
    private static readonly LibraryNoteRef Newton =
        LibraryNoteRef.Create("D5/L/Combinatorics/tao2026newton");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Realignment spectra and sharp elementary-symmetric tail bounds",
        H("Realignment spectra and elementary-symmetric separation"),
        Blocks(
            Entry("realign", "realign", "Realignment",
                "The complex bipartite matrix with entries indexed by (i,a) and (j,b) is rearranged into a rectangular matrix with row (i,j), column (a,b), and the same entry. The definition applies to arbitrary index types.", DescribeRole.Definition, true),
            Entry("singular-vector", "singularVector", "The row singular-value vector",
                "For a complex matrix on finite row and column types, this vector consists of the descending native singular values of its adjoint, through the row dimension. It therefore has the square of Alice's dimension entries for a realigned bipartite matrix. Zero values remain in the vector.", DescribeRole.Definition, true),
            Entry("esymm-sv", "esymmSV", "Elementary symmetric functions of singular values",
                "The degree ell elementary symmetric function is evaluated on the multiset of row singular values. Each subset of ell positions contributes the product of the corresponding singular values.", DescribeRole.Definition, true),
            Entry("esymm-vec", "esymmVec", "Elementary symmetric functions of finite real vectors",
                "For a vector of length k, the degree ell elementary symmetric function is evaluated on its complete multiset of entries, including repetitions and zeros.", DescribeRole.Definition, true),
            Entry("tail-mean", "tailMean", "The common tail coordinate",
                "For k coordinates and distinguished value a, the common tail value is (1-a)/(k-1). The natural subtraction in the denominator is retained in the definition.", DescribeRole.Definition),
            Entry("schur-profile", "schurProfile", "The one-heavy-coordinate profile",
                "The profile is choose(k-1,ell) times b to the ell plus choose(k-1,ell-1) times a times b to the ell-1, where b=(1-a)/(k-1). For k at least one and positive ell this is the elementary symmetric function at (a,b,...,b).", DescribeRole.Definition),
            Entry("separable-threshold", "separableThreshold", "The covariance tail threshold",
                "For natural local dimensions m and n, the threshold is one minus the square root of (1-1/m)(1-1/n).", DescribeRole.Definition),
            Entry("separable-threshold-one", "separableThreshold_lt_one", "The threshold is below one",
                "For local dimensions m and n at least two, the covariance tail threshold is strictly below one."),
            Entry("separable-threshold-uniform", "separableThreshold_gt_uniform", "The threshold exceeds the uniform coordinate",
                "For local dimensions m and n at least two, the covariance tail threshold strictly exceeds 1/m squared. The proof first bounds it strictly above 1/(2m)."),
            Entry("main-profile-gap", "main_profile_gap", "The main spectrum gives a strict scalar gap",
                "If 2 at most m is strictly less than n, n is at most m cubed, and 2 at most ell at most m squared, then the profile at the covariance threshold is strictly smaller than the profile at 1/sqrt(mn). This is a scalar comparison; it does not assert existence of a state with the prescribed spectrum."),
            Entry("uniform-profile-gap", "uniform_profile_gap", "The uniform spectrum gives a strict scalar gap",
                "For m and n at least two and 2 at most ell at most m squared, the profile at the covariance threshold is strictly smaller than its value at 1/m squared. This scalar inequality does not impose a dimensional condition for realizing the uniform spectrum."),
            Entry("exceptional-profile-gap", "exceptional_profile_gap", "The supported spectrum gives a strict scalar gap",
                "For m and n at least two and 2 at most ell at most m squared, the profile at the covariance threshold is strictly smaller than its value at 1/(m sqrt(m squared minus one)). The case m=2 is included by a separate rational comparison. This scalar inequality does not assert existence of a supported state."),
            Entry("esymm-replicate", "esymm_cons_replicate", "The exact multiset profile",
                "For natural N and j and arbitrary real a and b, the degree j+1 elementary symmetric function of one entry a and N copies of b equals choose(N,j+1) times b to the j+1 plus choose(N,j) times a times b to the j. Repeated and zero entries, arbitrary signs, and degrees exceeding the multiset size are included."),
            Entry("row-gram-spectrum", "singularVector_eq_sqrt_rowGram", "The row Gram spectral bridge",
                "For every complex matrix on finite row and column types and every row singular index, the native row singular value equals the square root of the corresponding descending eigenvalue of its positive row Gram matrix. This common bridge serves both the separable bound and the constructed witness spectra."),
            Entry("separable-esymm-bound", "separable_esymm_bound", "The universal separable realignment bound",
                "For natural dimensions 2 at most m strictly less than n, order ell from two through m squared, and every separable complex density matrix on their tensor product, the elementary symmetric singular-value function of its realignment is at most the profile at the covariance threshold. The live proof combines the real Hermitian-coordinate spectral transport and covariance tail constraints with the Newton and Maclaurin induction."),
            Describe.Lean(DescribeId.Create("tail-budget-sharp"),
                DeclarationHandle.Create(Prefix + "esymmVec_le_schurProfile_fin"),
                H("The sharp elementary-symmetric tail-budget bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Lps, Newton),
                Blocks(
                    Paragraph(Text("Let k be at least two and let ell lie from two through k. Suppose a nonnegative real vector s of length k has total mass at most one, the sum of all coordinates except index zero is at most 1-delta, and delta lies from 1/k through one. Then the degree ell elementary symmetric function of s is at most the one-heavy-coordinate profile at delta. No ordering hypothesis is required.")),
                    Paragraph(Text("Increase coordinate zero until the total mass is one, keeping the remaining entries fixed. Coordinate monotonicity does not decrease the symmetric function. The completed first coordinate a is at least delta. Splitting the symmetric function according to whether coordinate zero is selected leaves two elementary symmetric functions of the tail.")),
                    Paragraph(Text("Newton's inequality bounds every adjacent normalized coefficient ratio by the first ratio. Induction gives Maclaurin's bound: the degree j elementary symmetric function of N nonnegative entries is at most choose(N,j) times their arithmetic mean to the j. The proof first treats strictly positive entries and then passes to nonnegative entries by continuity after adding a common positive quantity. Applying this bound to both tail terms gives the profile at a. Its derivative is ((ell-1)/(k-1)) choose(k-1,ell-1) b to the ell-2 times (b-a), with b=(1-a)/(k-1). It is strictly negative inside the interval from 1/k to one; continuity includes both endpoints. This strict decrease gives the required profile bound at delta."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string declaration, string title, string text,
        DescribeRole role = DescribeRole.Theorem, bool literature = false) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(),
            literature ? AssessedProvenance.FromLiterature(Lps) : AssessedProvenance.FromRepo(Lps),
            Blocks(Paragraph(Text(text))), role);
}
