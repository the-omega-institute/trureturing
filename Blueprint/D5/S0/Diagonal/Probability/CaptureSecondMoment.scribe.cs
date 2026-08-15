using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Diagonal.Probability;

internal sealed class CaptureSecondMomentDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef PaleyZygmund =
        LibraryNoteRef.Create("D5/L/Diagonal/paleyzygmund1932analytic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite capture count has its exact variance identity and a Paley-Zygmund lower bound.",
        H("Capture Count Second Moment"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("capture-count-variance-and-second-moment-lower-bound"),
                DeclarationHandle.Create(
                    "D5/S0/Diagonal/Probability/CaptureSecondMoment."
                    + "capture_count_variance_and_lower_bound"),
                H("Capture count variance and second-moment lower bound"),
                StatementSource.FromAuthor(SecondMomentFormula()),
                AssessedProvenance.FromLiterature(PaleyZygmund),
                Blocks(
                    Paragraph(Text(
                        "Let N count addresses satisfying the frozen Captured predicate in the "
                        + "normalized finite independent-listing model. Its mean mu is the sum of "
                        + "the existing one-address capture probabilities. Its centered variance "
                        + "is E[N^2]-mu^2, and when E[N^2] is positive, the probability of at least "
                        + "one captured address is at least mu^2/E[N^2].")),
                    Paragraph(Text(
                        "The lower bound is the theta=0 case of the Paley-Zygmund inequality. The "
                        + "Lean proof applies Mathlib's finite Cauchy-Schwarz theorem directly to "
                        + "the weighted count and the indicator of the existing capture event; it "
                        + "does not introduce another capture predicate or probability model.")),
                    Paragraph(Text(
                        "Pinned-library searches found Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul "
                        + "but no packaged Paley-Zygmund theorem. Repository searches found exact "
                        + "one- and two-address laws and Bonferroni bounds, but no capture-count "
                        + "variance or second-moment lower bound."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S0/Asymptotics/WeightedProbability/FiniteProductCapture")),
        ]));

    private static Formula Probability(Formula eventFormula) => Seq(
        Operatorname, Grp(F.Id("P")), Open, eventFormula, Close);

    private static Formula Expectation(Formula value) => Seq(
        Operatorname, Grp(F.Id("E")), Open, value, Close);

    private static Formula SecondMomentFormula()
    {
        Formula address = F.Id("a");
        Formula count = F.Id("N");
        Formula mean = F.Id("mu");
        Formula captured = Call("Captured", address);
        Formula secondMoment = Expectation(Seq(count, Caret, Grp(D(2))));
        Formula anyCapture = Probability(Seq(Exists, Sp, address, Comma, Esc, captured));

        return Disp(Seq(
            mean, Eq, Sum, Underscore, Grp(address), Probability(captured),
            Sp, Land, Sp,
            Operatorname, Grp(F.Id("Var")), Open, count, Close, Eq,
            secondMoment, Minus, mean, Caret, Grp(D(2)),
            Sp, Land, Sp,
            Open, D(0), Lt, secondMoment, Sp, Rightarrow, Sp,
            Frac, Grp(mean, Caret, Grp(D(2))), Grp(secondMoment),
            Leq, anyCapture, Close, Dot));
    }
}
