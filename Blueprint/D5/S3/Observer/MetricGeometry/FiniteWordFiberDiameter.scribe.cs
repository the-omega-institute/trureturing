using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.MetricGeometry;

internal sealed class FiniteWordFiberDiameterDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A shared finite readout prefix gives a geometric prediction-distance bound.",
        H("Finite Readout Fiber Diameter"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("shared-finite-readout-prefix-bounds-prediction-distance"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/MetricGeometry/FiniteWordFiberDiameter."
                    + "finite_word_fiber_prediction_diameter"),
                H("A finite readout fiber has geometrically small prediction diameter"),
                StatementSource.FromAuthor(DiameterFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix an update, a readout, and a real-valued output discrepancy that "
                            + "vanishes on the diagonal. Assume all discrepancies are at most D "
                            + "and the discount factor gamma lies in (0, 1]. If two states have "
                            + "the same readout at update "
                            + "times zero through m, their discounted prediction distance is at "
                            + "most gamma to the power m plus one times D.")),
                    Paragraph(Text(
                        "For times through m, readout equality makes the discrepancy term zero. "
                            + "At every later time k, the global distance bound gives gamma to "
                            + "the power k times D, and geometric decay compares this with gamma "
                            + "to the power m plus one times D. Taking the supremum proves the "
                            + "claim.")),
                    Paragraph(Text(
                        "Loogle and LeanSearch found no full finite-prefix diameter theorem. The "
                            + "Lean proof applies the exact library results ciSup_le and "
                            + "pow_le_pow_of_le_one; repository and digestion-record searches "
                            + "found no duplicate."))),
                DescribeRole.Theorem))));

    private static Formula ReadoutAt(Formula state, Formula time) =>
        Seq(F.Id("q"), Open, Tau, Caret, Grp(time), Open, state, Close, Close);

    private static Formula PredictionDistance(Formula left, Formula right) =>
        Seq(F.Id("d"), Underscore, Grp(GammaLower), Open, left, Comma, Sp, right, Close);

    private static Formula DiameterFormula()
    {
        Formula k = F.Id("k");
        Formula m = F.Id("m");
        Formula y = F.Id("y");
        Formula yPrime = Seq(F.Id("y"), Apos);
        return Disp(Seq(
            D(0), Lt, GammaLower, Leq, D(1), Comma, Sp,
            Open, Forall, Sp, F.Id("a"), Comma, Esc,
            F.Id("d"), Underscore, Grp(F.Id("O")), Open, F.Id("a"), Comma, Sp,
            F.Id("a"), Close, Eq, D(0), Close, Comma, Esc,
            Open, Forall, Sp, F.Id("a"), Comma, Sp, F.Id("b"), Comma, Esc,
            F.Id("d"), Underscore, Grp(F.Id("O")), Open, F.Id("a"), Comma, Sp,
            F.Id("b"), Close, Sp, Leq, Sp, F.Id("D"), Close, Comma, Esc,
            Open, Forall, Sp, k, Sp, Leq, Sp, m, Comma, Esc,
            ReadoutAt(y, k), Eq, ReadoutAt(yPrime, k), Close,
            Sp, Rightarrow, Sp,
            PredictionDistance(y, yPrime), Sp, Leq, Sp,
            GammaLower, Caret, Grp(m, Plus, D(1)), Sp, F.Id("D"), Dot));
    }
}
