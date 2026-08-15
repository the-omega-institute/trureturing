using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Prediction;

internal sealed class EventualCycleAverageDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An eventually cyclic orbit has long-run observable average equal to its cycle average.",
        H("Eventual Cycle Average"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("eventually-cyclic-orbits-have-the-cycle-average"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Prediction/EventualCycleAverage."
                    + "eventual_cycle_average"),
                H("Eventually cyclic orbits have the cycle average"),
                StatementSource.FromAuthor(EventualCycleFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let update be a self-map of Y, let value be a real-valued "
                            + "observable, and start the orbit at initial. Assume there is "
                            + "a positive period lambda, an entry time mu, and a cycle p "
                            + "such that every iterate after mu is p indexed modulo lambda.")),
                    Paragraph(Text(
                        "Then the finite-horizon observable average converges to the uniform "
                            + "average of value over the cycle. The proof splits the orbit "
                            + "into its fixed prefix, complete cycle blocks, and one bounded "
                            + "remainder block.")),
                    Paragraph(Text(
                        "Loogle found the exact pinned-library limits "
                            + "tendsto_mod_div_atTop_nhds_zero_nat and "
                            + "tendsto_natCast_div_add_atTop; both are imported and applied. "
                            + "LeanSearch returned the convergent-sequence averaging theorem, "
                            + "fixed-point orbit averages, and bounded shift differences, but "
                            + "no nonconstant periodic-orbit average theorem. Repository and "
                            + "formalization searches found no duplicate. A one-state Boolean "
                            + "orbit witnesses satisfiable hypotheses."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Iterate(Formula exponent) =>
        Apply(Seq(F.Id("F"), Caret, Grp(exponent)), F.Id("a"));

    private static Formula CycleAt(Formula index) =>
        Seq(F.Id("p"), Underscore, Grp(index));

    private static Formula EventualCycleFormula()
    {
        Formula n = F.Id("n");
        Formula time = F.Id("t");
        Formula horizon = F.Id("T");
        Formula period = LambdaLower;
        Formula entry = Mu;
        Formula cycleIndex = Seq(n, Sp, Operatorname, Grp(F.Id("mod")), Sp, period);
        Formula orbitTerm = Apply(F.Id("v"), Iterate(time));
        Formula cycleTerm = Apply(F.Id("v"), CycleAt(F.Id("j")));

        return Disp(Seq(
            Forall, Sp, F.Id("Y"), Comma, Sp,
            F.Id("F"), Colon, Sp, F.Id("Y"), Sp, To, Sp, F.Id("Y"), Comma, Sp,
            F.Id("v"), Colon, Sp, F.Id("Y"), Sp, To, Sp, Mathbb, Grp(F.Id("R")),
            Comma, Sp, F.Id("a"), InMacro, Sp, F.Id("Y"), Comma, Esc,
            Forall, Sp, period, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            D(0), Sp, Lt, Sp, period, Comma, Sp,
            F.Id("p"), Colon, Sp, Operatorname, Grp(F.Id("Fin")), Open, period, Close,
            Sp, To, Sp, F.Id("Y"), Comma, Sp, entry, InMacro, Sp,
            Mathbb, Grp(F.Id("N")), Comma, Esc,
            Open, Forall, Sp, n, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            Iterate(Seq(entry, Plus, n)), Sp, Eq, Sp, CycleAt(cycleIndex), Close,
            Sp, Rightarrow, Esc,
            Lim, Underscore, Grp(horizon, To, Infty), Sp,
            Frac,
            Grp(Sum, Underscore, Grp(time, Eq, D(0)), Caret,
                Grp(horizon, Minus, D(1)), Sp, orbitTerm),
            Grp(horizon), Sp, Eq, Sp,
            Frac,
            Grp(Sum, Underscore, Grp(F.Id("j"), Eq, D(0)), Caret,
                Grp(period, Minus, D(1)), Sp, cycleTerm),
            Grp(period), Dot));
    }
}
