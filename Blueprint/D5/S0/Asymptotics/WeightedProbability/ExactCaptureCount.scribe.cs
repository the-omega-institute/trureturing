using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Asymptotics.WeightedProbability;

internal sealed class ExactCaptureCountDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Berman1972 =
        LibraryNoteRef.Create("D5/L/Diagonal/berman1972inclusion");

    public DocumentDefinition Create()
    {
        var a = F.Id("a");
        var address = F.Id("A");
        var b = F.Id("b");
        var f = F.Id("f");
        var j = F.Id("j");
        var q = F.Id("q");
        var s = F.Id("s");
        var set = F.Id("S");
        var additional = F.Id("U");
        var y = F.Id("y");
        var union = Call("union", set, additional);
        var unionCard = Seq(Lvert, Sp, union, Sp, Rvert);
        var captured = Call("Captured", f, s, a);
        var capturedSet = Seq(OpenBrace, a, InMacro, Sp, address, Sp, Mid, Sp,
            captured, CloseBrace);
        var countEvent = Call("eventProbability", q, Seq(
            OpenBrace, s, Sp, Mid, Sp,
            Lvert, Sp, capturedSet, Sp, Rvert, Sp, Eq, Sp, j, CloseBrace));
        var fixedPower = Call("fixedPowerMass", q, f, b, unionCard);
        var collisionPower = Call("collisionPowerMass", q, f, b, unionCard);
        var selected = Seq(b, InMacro, Sp, union);
        var product = Seq(Prod, Underscore, Grp(b, InMacro, Sp, address), Sp,
            Call("if", selected, fixedPower, collisionPower));
        var sign = Seq(Open, Minus, D(1), Close, Caret,
            Grp(Lvert, Sp, additional, Sp, Rvert));
        var exactMass = Seq(
            Sum, Underscore, Grp(set, Subseteq, Sp, address, Comma, Sp,
                Lvert, Sp, set, Sp, Rvert, Eq, j), Sp,
            Sum, Underscore, Grp(additional, Subseteq, Sp,
                Grp(address, Setminus, Sp, set)), Sp,
            sign, Sp, product);
        var qby = Seq(q, Underscore, Grp(b), Open, y, Close);

        return DocumentDefinition.Create(ScribeNode.Create(
            "Every finite capture-count value has an exact alternating-sum product mass.",
            H("Exact Capture Count Distribution"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("exact-weighted-mass-of-j-captured-addresses"),
                    DeclarationHandle.Create(
                        "D5/S0/Asymptotics/WeightedProbability/ExactCaptureCount."
                        + "exact_capture_count_probability"),
                    H("Exact mass of j captured addresses"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Forall, Sp, j, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
                        Open,
                        Forall, Sp, b, Comma, Esc,
                        Sum, Underscore, Grp(y), Sp, qby, Sp, Eq, Sp, D(1),
                        Close, Sp, Rightarrow, Sp,
                        countEvent, Sp, Eq, Sp, exactMass, Dot))),
                    AssessedProvenance.FromLiterature(Berman1972),
                    Blocks(
                        Paragraph(Text(
                            "Samples with capture count j are partitioned by their exact set S "
                            + "of addresses satisfying the frozen Captured predicate.")),
                        Paragraph(Text(
                            "For each S, complement inclusion-exclusion over addresses outside S "
                            + "gives the alternating sum over U. The imported exact prescribed-set "
                            + "law evaluates every S union U intersection as the displayed product.")),
                        Paragraph(Text(
                            "No nonnegativity premise is needed. Normalization is used only by the "
                            + "existing exact product-mass theorem."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Asymptotics/WeightedProbability/FiniteInclusionExclusion")),
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Asymptotics/WeightedProbability/FiniteProductSetCapture")),
            ]));
    }
}
