using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Asymptotics.Bonferroni;

internal sealed class TailBoundsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var address = F.Id("A");
        var captureCount = F.Id("N");
        var f = F.Id("f");
        var j = F.Id("j");
        var k = F.Id("k");
        var q = F.Id("q");
        var set = F.Id("T");
        Formula Moment(Formula degree)
        {
            var setRange = Grp(set, Subseteq, Sp, address, Comma, Sp,
                Lvert, Sp, set, Sp, Rvert, Eq, Sp, degree);
            return Seq(
                Sum, Underscore, setRange, Sp,
                Call("setCaptureProbability", q, f, set));
        }

        var countRange = Grp(D(0), Leq, Sp, j, Leq, Sp,
            Lvert, Sp, address, Sp, Rvert);
        var tail = Call("eventProbability", q, Seq(k, Leq, Sp, captureCount));
        var exactCountMass = Call("eventProbability", q,
            Seq(captureCount, Sp, Eq, Sp, j));
        var tailDecomposition = Seq(
            Sum, Underscore, Grp(countRange, Comma, Sp, k, Leq, Sp, j), Sp,
            exactCountMass);
        var kthMoment = Moment(k);
        var nextMoment = Moment(Seq(k, Plus, D(1)));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Positive capture-count tails are bounded above and below by consecutive binomial moments.",
            H("Capture-Count Tail Bounds"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("capture-count-tail-exact-count-decomposition"),
                    DeclarationHandle.Create(
                        "D5/S0/Asymptotics/Bonferroni/TailBounds."
                            + "capture_count_tail_eq_sum_exact"),
                    H("Tail mass decomposes by exact capture count"),
                    StatementSource.FromAuthor(Disp(Seq(
                        tail, Sp, Eq, Sp, tailDecomposition, Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The finite capture count takes one value between zero and the address cardinality. Splitting the weighted sample sum at that value expresses the tail as the disjoint sum of its exact-count masses."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("capture-count-tail-binomial-moment-upper-bound"),
                    DeclarationHandle.Create(
                        "D5/S0/Asymptotics/Bonferroni/TailBounds."
                            + "capture_count_tail_le_binomial_moment"),
                    H("The kth binomial moment bounds the kth tail from above"),
                    StatementSource.FromAuthor(Disp(Seq(
                        tail, Sp, Leq, Sp, kthMoment, Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "On every sample with at least k captures, choose(N,k) is at least one. Nonnegative sample weights preserve this pointwise inequality, and the exact binomial-moment identity converts the result to prescribed-set capture masses."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("consecutive-binomial-moment-tail-lower-bound"),
                    DeclarationHandle.Create(
                        "D5/S0/Asymptotics/Bonferroni/TailBounds."
                            + "binomial_moment_sub_k_next_le_capture_count_tail"),
                    H("Two consecutive moments bound the kth tail from below"),
                    StatementSource.FromAuthor(Disp(Seq(
                        kthMoment, Sp, Minus, Sp, k, Sp, Cdot, Sp, nextMoment,
                        Sp, Leq, Sp, tail, Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Pointwise, choose(N,k) minus k times choose(N,k+1) is at most the indicator of N at least k. The adjacent-binomial identity proves the inequality for all N, while nonnegative sample weights and the exact moment identity lift it to probabilities.")),
                        Paragraph(Text(
                            "The coefficient k is minimal among constants uniform in the capture count: at N equal to k plus one, the pointwise left side is k plus one minus c, so a valid coefficient c must be at least k. The compiled small-cardinality tables in the Lean module validate the boundary cases."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Asymptotics/WeightedProbability/BinomialMomentIdentity")),
            ]));
    }
}
