using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;

internal sealed class OriginalRectangleSmoothingDocument : IScribeDocumentDefinition
{
    private static DocumentBlock.Describe Entry(string id, string selector, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalRectangleSmoothing." + selector),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite original-record smoothing", H("Finite original-record smoothing"),
        Blocks(
            Entry("original-success-count", "originalSuccessCount", "Complete words in disjoint original blocks",
                "For a binary word w, a natural block length b, a number q of blocks and an original emitted record xs, the count inspects take(b,xs), adds one precisely when this entire block contains w as an infix, and then continues with drop(b,xs). It stops after q blocks. A successful block contributes once even when several occurrences overlap inside it. No hidden state enters this count.", DescribeRole.Definition),
            Entry("record", "record", "The finite exterior record",
                "For binary lists left and right, record fixes left on the original integer times from minus length(left) to minus one, and right from one to length(right). The missing center is at time zero. Empty lists impose no observation on their side.", DescribeRole.Definition),
            Entry("record-posterior", "recordPosterior", "The actual finite-record conditional probability",
                "For a visible measure P, the posterior is the real mass of the record together with center bit true divided by the real mass of the record. On a positive-likelihood record this is its actual center-bit conditional probability. Zero-mass records are left with the real division convention and carry zero weight.", DescribeRole.Definition),
            Entry("rectangle-minimum", "rectangleMinimum", "Exact lower rectangle entry",
                "The lower entry is the minimum of B(i,j) over the nonempty product of the exact support rows and columns. The support rectangle supplies strict positivity and zero entries outside that product.", DescribeRole.Definition),
            Entry("rectangle-maximum", "rectangleMaximum", "Exact upper rectangle entry",
                "The upper entry is the maximum over the same finite nonempty support product. Consequently the exact lower and upper entries u and v obey zero less than u less than or equal to v.", DescribeRole.Definition),
            Entry("finite-record-smoothing", "finite_record_smoothing_by_original_success_count", "Both actual posterior differences are bounded by counted original words",
                "Let H be any finite hidden state domain and theta a stationary nonnegative binary edge presentation, including structural zeros, zero initial coordinates, reducibility and periodicity. Let J be any probability measure satisfying theta's original hidden and visible cylinder identities. Let w be a nonempty original emitted word whose matrix product B has exact nonempty rectangular positive support. Set u and v to the exact minimum and maximum of B on that support, rho to one minus u divided by v, and b to length(w) plus the cardinality of H. For every extra past, common left record and common right record for which both compared events have positive likelihood, the absolute difference between the posteriors for extra-past followed by left and for left alone, with that same right, is at most rho to the left success count. If j is the length of left, discard its first j modulo b bits and count its floor(j/b) complete b-blocks, so the counted original clock interval ends at minus one. Symmetrically, every positive pair obtained by adding extra future to the right has difference at most rho to the count in the first floor(length(right)/b) original b-blocks of right, beginning at time one. These assertions include zero exterior message coordinates, zero counts, empty common records, and rho equal to zero, with zero to the zeroth power equal to one. No uniformity over presentations or parameter closures is asserted. The original-cylinder identities identify the actual record masses. Nonnegative numerator and denominator messages retain a common linear interval through ordinary observations. Across the rectangle, the same exterior likelihood gives a shared mass u/v and reduces the interval width by rho. Each disjoint successful block pays this reduction once; the reverse comparison uses transposed products on the same original records. The two positive record masses are normalized only after this common observation calculation, so no contraction of Bayesian prior normalization is used.", DescribeRole.Theorem))));
}
