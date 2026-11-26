using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Lattices;

internal sealed class HarderNarasimhanTruncationDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/grayson1984semistability");

    private static readonly LibraryNoteRef FrameSource =
        LibraryNoteRef.Create("D5/L/Zeros/alpoge2026riemann");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Harder-Narasimhan truncation and spectral deficit auxiliaries",
        H("High-slope prefixes and rank loss"),
        Blocks(
            Describe.Lean(DescribeId.Create("hn-threshold-truncation"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Lattices/HarderNarasimhanTruncation."
                    + "threshold_truncation"),
                H("A threshold splits the chain"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Let D be slope data on a lattice: rank is a "
                    + "strictly increasing integer-valued modular function and degree "
                    + "is a real-valued supermodular function. Given an HN chain from "
                    + "a to b and any real threshold t, there is an endpoint c and "
                    + "a prefix and suffix which concatenate to the original chain. "
                    + "Both segments are HN chains. If the prefix is nonzero then its "
                    + "minimal slope is at least t. If the suffix is nonzero then its "
                    + "maximal slope is strictly below t. The construction includes "
                    + "all factors whose slope equals the threshold in the prefix. "
                    + "Empty intervals and empty prefix or suffix are included."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hn-truncation-rank-deficit"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Lattices/HarderNarasimhanTruncation."
                    + "quantitative_truncation"),
                H("Exact deficit controls the deleted rank"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Suppose the maximal slope of the interval is "
                    + "at most s plus u and cut it at s minus tau. Write R for its "
                    + "rank and r for the suffix rank. The endpoint c can be chosen "
                    + "as above with (u plus tau) times r at most (s plus u) times R "
                    + "minus the interval degree. This undivided inequality needs "
                    + "no sign assumption and can be summed over a family of sources. "
                    + "When u plus tau is positive and the degree is at least s "
                    + "times R, it gives r at most u divided by (u plus tau) times R. "
                    + "If c is strictly below b, both the undivided inequality and "
                    + "the divided rank bound are strict under the same respective "
                    + "hypotheses: the nonempty suffix has maximal slope strictly "
                    + "below the threshold and positive rank. "
                    + "The prefix degree is bounded by its rank times the original "
                    + "maximal slope, and the suffix degree by its rank times the "
                    + "threshold. Their sum is the original degree. Thus the same "
                    + "bound applies when only a total mean inequality across sources "
                    + "is known, after summing the undivided inequalities."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hn-finite-slope-spectrum"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Lattices/HarderNarasimhanTruncation.hn_spectrum"),
                H("The finite slope spectrum and its level counts"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Repeat each factor slope according to that "
                    + "factor's positive integral rank. The resulting finite real list "
                    + "has length equal to the interval rank and sum equal to the "
                    + "interval degree. Every entry lies between the defined minimal "
                    + "and maximal slopes. For every real threshold, the number of "
                    + "entries strictly below it is exactly the rank of the suffix "
                    + "at the same HN truncation endpoint. Thus threshold dimension "
                    + "estimates and the finite slope distribution use a common "
                    + "realization, including slope equality at a cutoff."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hn-scalar-frame-rank-estimate"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Lattices/HarderNarasimhanTruncation."
                    + "scalar_rank_estimate"),
                H("A scalar comparison controls missing rank"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(FrameSource),
                Blocks(Paragraph(Text("For positive ambient dimension D and total source "
                    + "dimension R, suppose the real parameter w is at most D, "
                    + "rho is nonnegative, and e is at most one quarter. "
                    + "The trace t is at least R times one minus "
                    + "square root e. A nonnegative variance X is at most eta times "
                    + "t squared divided by D. If the partial trace z is at least "
                    + "t times w divided by D minus square root w times square "
                    + "root X, and at most R times the quantity rho plus square "
                    + "root of the product rho times e, then w is at most D times "
                    + "the quantity eta plus four rho plus four square root e. "
                    + "The hypotheses force eta nonnegative and the trace positive. "
                    + "Negative w is included, and negative e has real square root zero. "
                    + "The centered frame variance and partial trace bounds give "
                    + "these scalar hypotheses in the rank-coverage estimate."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hn-frame-variance-identity"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Lattices/HarderNarasimhanTruncation.variance_eq"),
                H("Centered symmetric operators have the trace variance"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(FrameSource),
                Blocks(Paragraph(Text("For a symmetric operator Q on a real inner "
                    + "product space of finite dimension D, subtract its "
                    + "trace divided by D times the identity. The squared "
                    + "Hilbert-Schmidt norm of this centered operator equals the "
                    + "trace of Q composed with itself minus its squared trace divided "
                    + "by D. At dimension zero both sides vanish under real division by zero. "
                    + "This trace identity is consumed by the frame variance "
                    + "and rank estimates, and is an algebraic auxiliary."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hn-finite-positive-spectral-deficit"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Lattices/HarderNarasimhanTruncation."
                    + "finite_spectral_deficit"),
                H("A reciprocal tail budget bounds positive spectral deficits"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(FrameSource),
                Blocks(Paragraph(Text("Let K be a nonempty finite target spectrum y. "
                    + "Assume u and H are nonnegative, each y is at least s minus "
                    + "H, and for every t from zero to H the number of entries "
                    + "below s minus t is at most D times the quantity eta plus "
                    + "four times u divided by (u plus t) plus four square root e. "
                    + "Then the sum of "
                    + "max(s minus y, zero) is at most D times G, where G is "
                    + "four u log(1 plus H divided by u) plus (eta plus four "
                    + "square root e) times H. The signed mean deficit is at "
                    + "most D divided by the cardinality of K times G. No "
                    + "dimension-ratio hypothesis is used. Integrating each "
                    + "positive deficit as a tail indicator retains its exact "
                    + "contribution; the zero-u branch has zero logarithmic term. "
                    + "This integration auxiliary is consumed by the compatible "
                    + "spectral-flags theorem in EuclideanCommonLattice."))),
                DescribeRole.Theorem))));
}
