using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.MetricGeometryLaws;

internal sealed class FirstDifferencePowerLawDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The discounted discrete prediction distance is the power of the first differing readout.",
        H("First Difference Power Law"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("first-difference-determines-discounted-distance"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/MetricGeometryLaws/FirstDifferencePowerLaw."
                        + "first_difference_power_law"),
                H("First difference determines discounted distance"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The relation R_q is equality of the q-readout at every iterate of the "
                            + "deterministic update tau. The distance is the existing discounted "
                            + "supremum using the discrete output discrepancy.")),
                    Paragraph(Text(
                        "If two states are R_q-related, every discrepancy term is zero. If they "
                            + "are distinguishable, Nat.find supplies the minimum time at which "
                            + "the readouts differ; all earlier terms vanish and later powers of "
                            + "gamma are no larger, giving the displayed power exactly.")),
                    Paragraph(Text(
                        "The theorem exposes both source clauses: zero distance on the relation "
                            + "and the first-difference power law for every separating witness."))),
                DescribeRole.Theorem))));

    private static Formula Apply(string name, params Formula[] arguments)
    {
        var content = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                content.Add(Comma);
                content.Add(Sp);
            }
            content.Add(arguments[index]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }

    private static Formula Apply(Formula name, params Formula[] arguments)
    {
        var content = new List<Formula> { name, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                content.Add(Comma);
                content.Add(Sp);
            }
            content.Add(arguments[index]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("Y");
        Formula output = F.Id("O");
        Formula tau = F.Id("tau");
        Formula readout = F.Id("q");
        Formula gamma = F.Id("gamma");
        Formula left = F.Id("y");
        Formula right = Seq(F.Id("y"), Apos);
        Formula time = F.Id("k");
        Formula relation = Apply("orbitReadoutRelation", tau, readout, left, right);
        Formula distance = Apply(
            "discountedPredictionDistance", tau, readout, gamma, left, right);
        Formula iterateLeft = Apply("iterate", tau, time, left);
        Formula iterateRight = Apply("iterate", tau, time, right);
        Formula readoutLeft = Apply(readout, iterateLeft);
        Formula readoutRight = Apply(readout, iterateRight);
        Formula separating = Seq(
            Exists, Sp, time, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            readoutLeft, Sp, Neq, Sp, readoutRight);
        Formula firstDifference = Apply(
            "firstDifferenceIndex", tau, readout, left, right);
        Formula power = Apply("pow", gamma, firstDifference);

        return Disp(Seq(
            Forall, Sp, state, Comma, Sp, output, Comma, Sp,
            OpenBracket, Call("DecidableEq", output), CloseBracket, Comma, Sp,
            tau, Colon, Sp, state, Sp, To, Sp, state, Comma, Sp,
            readout, Colon, Sp, state, Sp, To, Sp, output, Comma, Sp,
            gamma, Colon, Sp, Mathbb, Grp(F.Id("R")), Comma, Esc,
            Open, D(0), Sp, Lt, Sp, gamma, Sp, Leq, Sp, D(1), Close,
            Rightarrow, RowBreak, Grp(),
            Forall, Sp, left, Comma, Sp, right, InMacro, Sp, state, Comma, RowBreak,
            Grp(Open, relation, Rightarrow, Sp, distance, Sp, Eq, Sp, D(0), Close),
            Sp, Land, RowBreak,
            Grp(Open, separating, Rightarrow, Sp, distance, Sp, Eq, Sp, power, Close), Dot));
    }
}
