using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Thresholds;

internal sealed class PeriodicThresholdKernelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reachable periodic states exactly control eventual threshold bounds on finite orbits.",
        H("Periodic Threshold Kernel"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("eventual-thresholds-are-controlled-by-reachable-periodic-states"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Thresholds/PeriodicThresholdKernel."
                    + "eventual_threshold_iff_reachable_periodic"),
                H("Eventual thresholds are controlled by reachable periodic states"),
                StatementSource.FromAuthor(ThresholdFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let Y be a finite state carrier, F a deterministic self-map, A a set "
                            + "of allowed initial states, and v a real-valued observable. Write "
                            + "P_F(A) for the states on positive-period F-orbits that are reached "
                            + "by some finite iterate of a state in A.")),
                    Paragraph(Text(
                        "There is one time N after which every orbit from A has value at most "
                            + "alpha if and only if every state in P_F(A) has value at most alpha. "
                            + "The reverse implication uses N equal to the number of states: by "
                            + "then every trajectory is in its reachable periodic core.")),
                    Paragraph(Text(
                        "Repository search found and the proof applies the weaker quantitative "
                            + "finite-orbit period bound. Pinned Mathlib supplied periodicPts, "
                            + "IsPeriodicPt.mul_const, and iterate_add_apply, but no theorem with "
                            + "the full threshold equivalence. Three local smart-search queries "
                            + "also returned no full match. Loogle and LeanSearch were absent "
                            + "from the available NyxID services; two GitHub code-search proxy "
                            + "requests failed with HTTP 400 and supplied no conclusion."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Iterate(Formula exponent, Formula state) =>
        Seq(F.Id("F"), Caret, Grp(exponent), Open, state, Close);

    private static Formula PeriodicCore() =>
        Seq(F.Id("P"), Underscore, Grp(F.Id("F")), Open, F.Id("A"), Close);

    private static Formula ThresholdFormula()
    {
        Formula carrier = F.Id("Y");
        Formula time = F.Id("t");
        Formula start = F.Id("a");
        Formula state = F.Id("p");
        Formula value = F.Id("v");
        return Disp(Seq(
            Forall, Sp, carrier, Comma, Sp,
            OpenBracket, Operatorname, Grp(F.Id("Finite")), Open, carrier, Close,
            CloseBracket, Comma, Esc,
            F.Id("F"), Colon, Sp, carrier, Sp, To, Sp, carrier, Comma, Sp,
            F.Id("A"), Sp, Subseteq, Sp, carrier, Comma, Sp,
            value, Colon, Sp, carrier, Sp, To, Sp, Mathbb, Grp(F.Id("R")),
            Comma, Sp, Alpha, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Esc,
            Open, Exists, Sp, F.Id("N"), InMacro, Sp, Mathbb, Grp(F.Id("N")),
            Comma, Esc, Forall, Sp, start, InMacro, Sp, F.Id("A"), Comma, Sp,
            time, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
            F.Id("N"), Sp, Leq, Sp, time, Sp, Rightarrow, Sp,
            Apply(value, Iterate(time, start)), Sp, Leq, Sp, Alpha, Close,
            Sp, Iff, Sp,
            Forall, Sp, state, InMacro, Sp, PeriodicCore(), Comma, Esc,
            Apply(value, state), Sp, Leq, Sp, Alpha, Dot));
    }
}
