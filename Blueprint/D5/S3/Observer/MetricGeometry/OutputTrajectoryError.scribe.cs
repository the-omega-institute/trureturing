using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.MetricGeometry;

internal sealed class OutputTrajectoryErrorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Output-orbit error is controlled by readout mismatch and accumulated transition defect.",
        H("Output Trajectory Error"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("output-trajectory-error-bound"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/MetricGeometry/OutputTrajectoryError."
                    + "output_trajectory_error"),
                H("Output trajectory error bound"),
                StatementSource.FromAuthor(OutputErrorFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume the abstract update is L-Lipschitz, the abstract readout is "
                        + "M-Lipschitz, every one-step projection defect is at most delta, "
                        + "and every current readout mismatch is at most eta. Then the output "
                        + "error after k updates is bounded by eta plus M times the transition "
                        + "defect accumulated through the finite geometric sum.")),
                    Paragraph(Text(
                        "The proof first bounds projection-orbit error by induction. At the "
                        + "successor step it inserts the k-fold abstract update of the projected "
                        + "next state. The induction hypothesis controls the first distance, "
                        + "while the imported Lipschitz iterate bound controls the second.")),
                    Paragraph(Text(
                        "Finally, insert the abstract readout of the projected concrete orbit. "
                        + "The triangle inequality separates current readout mismatch from "
                        + "propagated orbit error, and the M-Lipschitz estimate gives the stated "
                        + "bound. The statement includes k=0, where the geometric sum is empty.")),
                    Paragraph(Text(
                        "Loogle found the exact supporting declarations LipschitzWith.iterate "
                        + "and LipschitzWith.edist_le_mul_of_le, which are imported and applied. "
                        + "No full-statement match was found by Loogle, LeanSearch, or repository "
                        + "search."))),
                DescribeRole.Theorem))));

    private static Formula Iterate(Formula map, Formula exponent, Formula state) =>
        Seq(map, Caret, Grp(exponent), Open, state, Close);

    private static Formula OutputErrorFormula()
    {
        Formula k = F.Id("k");
        Formula j = F.Id("j");
        Formula y = F.Id("y");
        Formula concreteOrbit = Iterate(Tau, k, y);
        Formula abstractOrbit = Iterate(SigmaLower, k, Seq(Pi, Sp, y));
        Formula geometricSum = Seq(
            Sum, Underscore, Grp(Seq(j, Eq, D(0))), Caret,
            Grp(Seq(k, Minus, D(1))), Sp,
            F.Id("L"), Caret, Grp(j));
        return Disp(Seq(
            Forall, Sp, k, InMacro, Mathbb, Grp(F.Id("N")), Comma, Sp,
            Forall, Sp, y, InMacro, Sp, F.Id("Y"), Comma, Esc,
            F.Id("d"), Underscore, Grp(F.Id("O")), Open,
            F.Id("q"), Open, concreteOrbit, Close, Comma, Sp,
            F.Id("o"), Open, abstractOrbit, Close, Close, Sp,
            Leq, Sp, F.Id("eta"), Sp, Plus, Sp, F.Id("M"), DeltaLower, Sp,
            geometricSum, Dot));
    }
}
