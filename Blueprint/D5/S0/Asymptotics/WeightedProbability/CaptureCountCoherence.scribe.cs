using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Asymptotics.WeightedProbability;

internal sealed class CaptureCountCoherenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var a = F.Id("a");
        var address = F.Id("A");
        var b = F.Id("b");
        var f = F.Id("f");
        var j = F.Id("j");
        var q = F.Id("q");
        var set = F.Id("S");
        var additional = F.Id("U");
        var y = F.Id("y");
        var union = Call("union", set, additional);
        var unionCard = Seq(Lvert, Sp, union, Sp, Rvert);
        var qby = Seq(q, Underscore, Grp(b), Open, y, Close);
        var fixedPower = Call("fixedPowerMass", q, f, b, unionCard);
        var collisionPower = Call("collisionPowerMass", q, f, b, unionCard);
        var selected = Seq(b, InMacro, Sp, union);
        var product = Seq(Prod, Underscore, Grp(b, InMacro, Sp, address), Sp,
            Call("if", selected, fixedPower, collisionPower));
        var sign = Seq(Open, Minus, D(1), Close, Caret,
            Grp(Lvert, Sp, additional, Sp, Rvert));
        var exactMass = Seq(
            Sum, Underscore, Grp(set, Subseteq, Sp, address, Comma, Sp,
                Lvert, Sp, set, Sp, Rvert, Eq, Sp, j), Sp,
            Sum, Underscore, Grp(additional, Subseteq, Sp,
                Grp(address, Setminus, Sp, set)), Sp,
            sign, Sp, product);
        var countRange = Grp(D(0), Leq, Sp, j, Leq, Sp,
            Lvert, Sp, address, Sp, Rvert);
        var distributionSum = Seq(Sum, Underscore, countRange, Sp, exactMass);
        var firstMoment = Seq(Sum, Underscore, countRange, Sp, j, Sp, exactMass);
        var normalization = Seq(
            Forall, Sp, b, Comma, Esc,
            Sum, Underscore, Grp(y), Sp, qby, Sp, Eq, Sp, D(1));
        var nonnegative = Seq(
            Forall, Sp, b, Comma, Sp, y, Comma, Esc,
            D(0), Leq, Sp, qby);
        var captureMean = Seq(
            Sum, Underscore, Grp(a, InMacro, Sp, address), Sp,
            Call("captureProbability", q, f, a));

        return DocumentDefinition.Create(ScribeNode.Create(
            "The exact finite capture-count distribution is coherent with total mass and its independently computed mean.",
            H("Capture Count Coherence"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("exact-capture-count-distribution-normalization"),
                    DeclarationHandle.Create(
                        "D5/S0/Asymptotics/WeightedProbability/CaptureCountCoherence."
                        + "exact_capture_count_probability_normalizes"),
                    H("Normalization of the exact capture-count distribution"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Open, normalization, Close, Sp, Rightarrow, Sp,
                        distributionSum, Sp, Eq, Sp, D(1), Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Rewriting every explicit mass by the frozen exact capture-count theorem reduces the sum to a partition of all samples by their unique realized count.")),
                        Paragraph(Text(
                            "The count lies between zero and |A|, so exactly one term survives; the frozen total sample-weight identity then gives one."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("exact-capture-count-distribution-mean-agreement"),
                    DeclarationHandle.Create(
                        "D5/S0/Asymptotics/WeightedProbability/CaptureCountCoherence."
                        + "exact_capture_count_probability_mean_agreement"),
                    H("Mean agreement for the exact capture-count distribution"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Open, nonnegative, Close, Sp, Land, Sp,
                        Open, normalization, Close, Sp, Rightarrow, Sp,
                        firstMoment, Sp, Eq, Sp, captureMean, Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The explicit law again selects the unique realized count for each sample, and the cardinality is rewritten as the sum of its capture indicators.")),
                        Paragraph(Text(
                            "The resulting weighted indicator sum is identified with the independently frozen first-moment calculation from CaptureSecondMoment."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Asymptotics/WeightedProbability/ExactCaptureCount")),
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Diagonal/Probability/CaptureSecondMoment")),
            ]));
    }
}
