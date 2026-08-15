using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Asymptotics.WeightedProbability;

internal sealed class FiniteInclusionExclusionDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Berman1972 =
        LibraryNoteRef.Create("D5/L/Diagonal/berman1972inclusion");

    private static readonly LibraryNoteRef Galambos1977 =
        LibraryNoteRef.Create("D5/L/Diagonal/galambos1977bonferroni");

    public DocumentDefinition Create()
    {
        var a = F.Id("a");
        var b = F.Id("b");
        var f = F.Id("f");
        var q = F.Id("q");
        var s = F.Id("s");
        var t = F.Id("T");
        var address = F.Id("A");
        var y = F.Id("y");
        var captured = Call("Captured", f, s, a);
        var someCapture = Call("eventProbability", q, Seq(
            OpenBrace, s, Sp, Mid, Sp, Exists, Sp, a, Comma, Esc,
            captured, CloseBrace));
        var allInT = Call("eventProbability", q, Seq(
            OpenBrace, s, Sp, Mid, Sp, Forall, Sp, a, InMacro, Sp, t,
            Comma, Esc, captured, CloseBrace));
        var sign = Seq(Open, Minus, D(1), Close, Caret,
            Grp(Lvert, Sp, t, Sp, Rvert, Plus, D(1)));
        var exactSum = Seq(Sum, Underscore,
            Grp(Emptyset, Neq, Sp, t, Sp, Subseteq, Sp, address),
            sign, Sp, allInT);
        var escape = Call("escapeProbability", q, f);
        var degreeOne = Seq(Sum, Underscore,
            Grp(t, Subseteq, Sp, address, Comma, Sp,
                Lvert, Sp, t, Sp, Rvert, Eq, D(1)), allInT);
        var degreeTwo = Seq(Sum, Underscore,
            Grp(t, Subseteq, Sp, address, Comma, Sp,
                Lvert, Sp, t, Sp, Rvert, Eq, D(2)), allInT);
        var qby = Seq(q, Underscore, Grp(b), Open, y, Close);

        return DocumentDefinition.Create(ScribeNode.Create(
            "Finite weighted capture is exactly the alternating sum of all nonempty intersection events.",
            H("Finite Capture Inclusion-Exclusion"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("weighted-capture-inclusion-exclusion"),
                    DeclarationHandle.Create(
                        "D5/S0/Asymptotics/WeightedProbability/FiniteInclusionExclusion."
                        + "capture_event_inclusion_exclusion"),
                    H("Exact weighted capture inclusion-exclusion"),
                    StatementSource.FromAuthor(Disp(Seq(
                        someCapture, Sp, Eq, Sp, exactSum, Dot))),
                    AssessedProvenance.FromLiterature(Berman1972),
                    Blocks(
                        Paragraph(Text(
                            "Mathlib's pointwise finite-union indicator identity is applied directly to the captured-address events and then summed against sampleWeight.")),
                        Paragraph(Text(
                            "The identity is linear, so it requires neither nonnegative weights nor normalized marginals."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("bonferroni-bounds-are-the-first-two-truncations"),
                    DeclarationHandle.Create(
                        "D5/S0/Asymptotics/WeightedProbability/FiniteInclusionExclusion."
                        + "escape_bonferroni_truncations_of_inclusion_exclusion"),
                    H("The first two truncations are the frozen escape sandwich"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Open,
                        Forall, Sp, b, Comma, Sp, y, Comma, Esc,
                        D(0), Leq, Sp, qby,
                        Sp, Land, Sp,
                        Forall, Sp, b, Comma, Esc,
                        Sum, Underscore, Grp(y), Sp, qby, Sp, Eq, Sp, D(1),
                        Close, Sp, Rightarrow, Sp,
                        D(1), Minus, degreeOne, Sp, Leq, Sp, escape,
                        Sp, Leq, Sp,
                        D(1), Minus, degreeOne, Plus, degreeTwo, Dot))),
                    AssessedProvenance.FromLiterature(Galambos1977),
                    Blocks(
                        Paragraph(Text(
                            "The degree-one subset sum is proved equal to the frozen captureProbability sum.")),
                        Paragraph(Text(
                            "A bijection from strictly ordered pairs to two-element subsets proves that the degree-two subset sum is the frozen pairProbabilitySum. Rewriting by those two public lemmas reduces the result exactly to the imported frozen escape_bonferroni_bounds theorem."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Asymptotics/WeightedProbability/FiniteBonferroni")),
            ]));
    }
}
