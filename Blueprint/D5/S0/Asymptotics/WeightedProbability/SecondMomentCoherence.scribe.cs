using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Asymptotics.WeightedProbability;

internal sealed class SecondMomentCoherenceDocument : IScribeDocumentDefinition
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
        var secondMoment = Seq(Sum, Underscore, countRange, Sp,
            j, Caret, Grp(D(2)), Sp, exactMass);
        var normalization = Seq(
            Forall, Sp, b, Comma, Esc,
            Sum, Underscore, Grp(y), Sp, qby, Sp, Eq, Sp, D(1));
        var nonnegative = Seq(
            Forall, Sp, b, Comma, Sp, y, Comma, Esc,
            D(0), Leq, Sp, qby);
        var captureSum = Seq(
            Sum, Underscore, Grp(a, InMacro, Sp, address), Sp,
            Call("captureProbability", q, f, a));
        var pairSum = Call("pairProbabilitySum", q, f);
        var frozenSecondMoment = Seq(captureSum, Sp, Plus, Sp, D(2), Sp, pairSum);

        return DocumentDefinition.Create(ScribeNode.Create(
            "The exact finite capture-count distribution reproduces its independently frozen second moment.",
            H("Second Moment Coherence"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("exact-capture-count-second-moment-agreement"),
                    DeclarationHandle.Create(
                        "D5/S0/Asymptotics/WeightedProbability/SecondMomentCoherence."
                        + "exact_capture_count_probability_second_moment_agreement"),
                    H("Second moment agreement for the exact capture-count distribution"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Open, nonnegative, Close, Sp, Land, Sp,
                        Open, normalization, Close, Sp, Rightarrow, Sp,
                        secondMoment, Sp, Eq, Sp, frozenSecondMoment, Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The explicit alternating-product law selects the unique realized count for each sample, and the squared cardinality is rewritten as the square of its capture-indicator sum.")),
                        Paragraph(Text(
                            "The resulting weighted sum is identified with the independently frozen indicator-square second moment, which expands as the one-address probability sum plus twice the unordered two-address sum."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Asymptotics/WeightedProbability/CaptureCountCoherence")),
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Diagonal/Probability/CaptureCountMoments")),
            ]));
    }
}
