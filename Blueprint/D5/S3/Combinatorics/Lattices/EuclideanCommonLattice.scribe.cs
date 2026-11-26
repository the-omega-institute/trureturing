using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Lattices;

internal sealed class EuclideanCommonLatticeDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef FrameSource =
        LibraryNoteRef.Create("D5/L/Zeros/alpoge2026riemann");
    private static readonly LibraryNoteRef HnSource =
        LibraryNoteRef.Create("D5/L/QuadraticForms/grayson1984semistability");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Common integral Euclidean lattices and nearly orthogonal frames",
        H("A shared integral target controls the average slope"),
        Blocks(
            Describe.Lean(DescribeId.Create("common-integral-frame-slope"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Lattices/EuclideanCommonLattice."
                    + "common_lattice_slope"),
                H("The common-lattice frame slope inequality"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(FrameSource),
                Blocks(
                    Paragraph(Text("The source lattices span their finite-dimensional real "
                        + "inner product spaces, whose dimensions are the source "
                        + "matrix column counts. The common target C is any discrete "
                        + "integral submodule of W; its real span may be proper. "
                        + "The slope is minus the logarithm of the "
                        + "Gram covolume divided by integral rank. Source dimensions "
                        + "may vanish individually, but their sum R is positive. "
                        + "The source maps B preserve the common target lattice C. "
                        + "For a nonzero map, its height is the logarithm of its "
                        + "operator norm, bounded by the declared height. The padded "
                        + "frame maps A have an "
                        + "arbitrary common surjective coordinate projection P with "
                        + "P composed with each A equal to the corresponding B.")),
                    Paragraph(Text("Suppose the dimension-weighted average source "
                        + "slope minus height is at least s. For every source of "
                        + "positive integral rank, its maximal slope minus height "
                        + "is at most s plus u. Zero-rank sources impose no such "
                        + "condition. The target "
                        + "minimal slope is at least s minus H, with H nonnegative. "
                        + "The squared "
                        + "Hilbert-Schmidt Gram errors sum to at most e times R, "
                        + "with e strictly below one. This includes the original "
                        + "range e at most one quarter. The frame operator Q has "
                        + "trace of its square at most one plus eta times its "
                        + "squared trace divided by padded dimension D. The target "
                        + "ambient dimension d is positive. The real weights are "
                        + "arbitrary, and u, e and eta are nonnegative as consequences "
                        + "of the hypotheses rather than additional assumptions.")),
                    Paragraph(Text("Write G for four u log(1 plus H divided by u) "
                        + "plus (eta plus four square root e) times H. The theorem "
                        + "gives s minus the target average slope at most D divided "
                        + "by d times G. Writing m for the integral rank of C, it "
                        + "also gives m times this slope deficit plus (d minus m) "
                        + "times H at most D times G. Both conclusions retain the "
                        + "original ambient dimension d. For every delta below one "
                        + "such that (1 minus delta) times D is at most d, the "
                        + "original bound G divided by (1 minus delta) follows as "
                        + "a further conclusion of the same theorem. At u equal to "
                        + "zero the logarithmic term is zero. There is no logarithm "
                        + "of the number of source lattices.")),
                    Paragraph(Text("At threshold s minus tau plus the source height, "
                        + "the HN prefix has the exact rank counted by the source "
                        + "spectrum above that threshold. The average and maximal "
                        + "source bounds give total discarded rank at most "
                        + "u divided by (u plus tau) times R. If an integral image "
                        + "of a high source prefix had a nonzero class modulo the "
                        + "target high prefix, the relative morphism slope "
                        + "inequality would contradict the target low-tail maximal "
                        + "slope. Thus all these images lie in the same target "
                        + "prefix. Rank coverage bounds its codimension. The "
                        + "integral of the target spectral deficit and the "
                        + "identity integrating u divided by (u plus tau) yield "
                        + "the displayed logarithmic term.")),
                    Paragraph(Text("If C has rank m in ambient dimension d, append "
                        + "d minus m auxiliary target slopes equal to s minus H. "
                        + "Before the endpoint H, their low-level count is exactly "
                        + "the ambient dimension missing from the span of C. At H "
                        + "the target flag is the full padded space, and the strict "
                        + "low-level count is zero. Integrating the positive part "
                        + "of the padded spectrum deficit retains the entire "
                        + "(d minus m) times H contribution, giving the weighted "
                        + "bound before any average comparison. The augmented average is at "
                        + "most the actual target slope, since every original "
                        + "slope is at least s minus H. Rank zero is included with "
                        + "both extreme and average slopes zero. Thus the argument "
                        + "keeps the original ambient dimension d throughout; it "
                        + "does not replace W by the span of C.")),
                    Paragraph(Text("Grayson's semistability filtration supplies the "
                        + "classical HN setting. The concrete Gram lattice theory, "
                        + "the relative morphism proof, threshold multiplicity "
                        + "construction and real operator realization are proved "
                        + "in this library. The comparison source for the frame "
                        + "statement is Alpoge's TheoremFSharp and its proof "
                        + "frame_theorem_sharp. The full number-field theorem is "
                        + "not identified with an arbitrary real lattice."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("spectral-frame-slope"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Lattices/EuclideanCommonLattice.spectral_frame_slope"),
                H("A logarithmic slope bound from compatible spectral flags"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(FrameSource),
                Blocks(
                    Paragraph(Text("Let the sources and common target be finite-dimensional "
                        + "real inner product spaces. A finite spectrum on each source has "
                        + "one entry per source dimension. Let y be a finite target "
                        + "spectrum, and write d for its cardinality and D for the ambient "
                        + "target dimension. The total source dimension R is positive. "
                        + "For each real threshold parameter t between zero and H, choose "
                        + "source and target subspaces. The source codimension counts "
                        + "entries below s minus t, the target codimension counts entries "
                        + "of y below the same threshold, and every source image lies in "
                        + "the chosen target subspace.")),
                    Paragraph(Text("Assume that H is nonnegative, every source "
                        + "spectral entry is at most s plus u, and the sum of the source "
                        + "entries is at least R times s. Every target entry is at least "
                        + "s minus H. Let e be less than one and d be positive. "
                        + "No dimension-ratio parameter is required. The real frame weights "
                        + "may be arbitrary real numbers. Its sum of squared "
                        + "Hilbert-Schmidt source Gram errors is at most e times R. "
                        + "The trace of the square of its target frame operator is "
                        + "at most the product of one plus eta and its squared trace, divided "
                        + "by D.")),
                    Paragraph(Text("Write G for four u times log of one plus H divided "
                        + "by u, plus H times eta plus four square root e. The sum "
                        + "over all target entries of max of s minus y and zero is "
                        + "at most D times G. Also s minus the average of y is at "
                        + "most D divided by d times G. This preserves the exact "
                        + "dimension ratio and the positive-part information. At u "
                        + "equal to zero the logarithmic term is zero. Empty individual "
                        + "source spectra are permitted, but R must remain positive. "
                        + "The hypotheses force u, e and eta to be nonnegative. "
                        + "Weights may be arbitrary real numbers. If d is at least "
                        + "one minus delta times D and delta is below one, the exact "
                        + "ratio recovers the original one over one minus delta bound.")),
                    Paragraph(Text("The total number of source entries below the "
                        + "threshold is bounded by u divided by u plus t times R. "
                        + "The frame energy estimates bound the image codimension "
                        + "by eta plus four times this deleted fraction plus four "
                        + "times the square root of e, multiplied by D. Image "
                        + "placement transfers this estimate to the target tail. "
                        + "Integrating its counting function bounds the positive "
                        + "spectral deficits, which dominate the signed average "
                        + "deficit. The reciprocal integral is u times log of one "
                        + "plus H divided by u.")),
                    Paragraph(Text("Compatibility of the flags is an explicit "
                        + "hypothesis. In an integral lattice application, source "
                        + "entries are the actual Harder-Narasimhan slopes minus "
                        + "the corresponding declared map height, repeated with "
                        + "rank multiplicities. The target entries start with "
                        + "the actual spectrum of C. If C does not span W, append "
                        + "dim W minus the rank of C additional entries equal "
                        + "to the floor s minus H. The lower slope bound makes "
                        + "this augmented average at most the average slope of C, "
                        + "including its zero-rank convention.")),
                    Paragraph(Text("For a threshold parameter tau strictly below H, "
                        + "use the real span of the actual target high-slope "
                        + "prefix. At tau equal to H use the whole space W. "
                        + "The codimension of this flag equals the strict "
                        + "lower-level count in the augmented spectrum: below H, "
                        + "the additional floor entries count the dimensions "
                        + "outside the span of C; at H no entry lies below "
                        + "the floor. With a padded target, take the inverse "
                        + "image of this flag under the surjective coordinate "
                        + "projection, which preserves its codimension. The "
                        + "integral morphism comparison supplies image placement "
                        + "in the actual high-slope prefix. The whole target "
                        + "space supplies the endpoint flag."))),
                DescribeRole.Theorem),
            Describe.Remark(DescribeId.Create("common-lattice-normalization"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Lattices/EuclideanCommonLattice.spectral_frame_slope"),
                H("Relation to the common integral lattice estimate"),
                AssessedProvenance.FromRepo(FrameSource),
                Blocks(Paragraph(Text("Alpoge's TheoremFSharp and frame_theorem_sharp "
                    + "use Hermitian lattices over a totally complex number field. "
                    + "Within a fixed class of subobjects, multiplying every slope "
                    + "by two and adding a common constant, multiplying heights "
                    + "by two, applying the same affine change to s, and doubling "
                    + "u and H preserves both constants four in the homogeneous "
                    + "inequality. This is a comparison of linear normalizations "
                    + "on the same objects and the same subobject category.")),
                    Paragraph(Text("The number-field height is twice the average "
                        + "of the logarithmic operator norms over the complex "
                        + "places. The logarithmic operator norm of the induced "
                        + "map on the real orthogonal direct sum is the maximum "
                        + "of those logarithmic norms. Average and maximum are "
                        + "not identified. Moreover, saturated subobjects over "
                        + "the ring of integers differ from all saturated "
                        + "integer sublattices of the underlying real lattice. "
                        + "An affine identity for average degrees does not "
                        + "identify their maximal slopes, minimal slopes or "
                        + "Harder-Narasimhan spectra.")),
                    Paragraph(Text("Realification of the complex frame operators "
                        + "doubles their dimensions, traces and squared "
                        + "Hilbert-Schmidt norms, preserving the normalized "
                        + "parameters e and eta. The real finite spectral result "
                        + "retains both constants four. Its error range e less "
                        + "than one contains the source range e at most one "
                        + "quarter: above one quarter, the full target dimension "
                        + "already bounds the image codimension by the stated "
                        + "error. The integral morphism comparison for real "
                        + "integer lattices requires its own proof; it is not "
                        + "a direct specialization of the number-field theorem.")))),
            Describe.Remark(DescribeId.Create("integrality-boundary"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Lattices/EuclideanCommonLattice.spectral_frame_slope"),
                H("Why exact frame data do not replace common integrality"),
                AssessedProvenance.FromRepo(FrameSource),
                Blocks(Paragraph(Text("In one real dimension take N to be the integers, "
                    + "C to be q times the integers for an integer q greater than one, "
                    + "and B, A and the frame weight all equal to one. The source "
                    + "slope and map height are zero, the target slope is minus "
                    + "log q, and both frame errors vanish. Set s, u, e, eta and "
                    + "delta to zero, and H to log q. Omitting integrality would "
                    + "give log q at most zero. The actual obstruction is that "
                    + "B does not carry N into C. The integral map given by "
                    + "multiplication by q has height log q, restoring the cost. "
                    + "This is the real integer-lattice counterpart of the "
                    + "Gaussian-integer example in the source discussion.")))),
            Describe.Remark(DescribeId.Create("error-endpoint-boundary"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Lattices/EuclideanCommonLattice.spectral_frame_slope"),
                H("The error endpoint needs a separate variance sign condition"),
                AssessedProvenance.FromRepo(FrameSource),
                Blocks(Paragraph(Text("At e equal to one, take one-dimensional sources "
                    + "and target, a zero frame map, source spectrum zero, target "
                    + "spectrum minus one, s and u zero, H one, and delta zero. "
                    + "The source Gram error is one and the target frame operator "
                    + "is zero. Its moment inequality permits every eta, including "
                    + "eta equal to minus five. The compatible source flag is the "
                    + "whole source; the target flag is zero below threshold "
                    + "parameter one and the whole target at one. The proposed "
                    + "upper bound would then be minus one, whereas the slope "
                    + "deficit is one. Thus the endpoint cannot be included when "
                    + "eta has no separate nonnegativity hypothesis.")))),
            Describe.Remark(DescribeId.Create("euclidean-hn-source"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Lattices/EuclideanCommonLattice.spectral_frame_slope"),
                H("Arithmetic spectra require the Euclidean filtration"),
                AssessedProvenance.FromLiterature(HnSource),
                Blocks(Paragraph(Text("Grayson's semistability filtration supplies "
                    + "the classical Euclidean-lattice setting for the arithmetic "
                    + "spectra. The finite spectral theorem imposes its own "
                    + "multiplicity and image-placement hypotheses, and makes "
                    + "no assertion that arbitrary real spectra arise from "
                    + "a discrete integral lattice.")))))));
}
