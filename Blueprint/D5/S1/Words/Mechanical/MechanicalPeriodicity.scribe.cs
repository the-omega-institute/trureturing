using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Mechanical;

internal sealed class MechanicalPeriodicityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Classify eventual periodicity of lower mechanical words by rationality of the slope.",
        H("Periodicity of Lower Mechanical Words"),
        Blocks(
            Paragraph(Text(
                "Fix a real slope alpha in the half-open interval from zero to one and an arbitrary "
                + "real intercept rho. A rational slope gives a period from the reduced denominator. "
                + "Conversely, exact repetition on a tail and the frozen discrepancy bound force "
                + "the slope to equal a quotient of two natural numbers.")),
            Describe.Lean(
                DescribeId.Create("lower-mechanical-eventual-periodicity"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Mechanical/MechanicalPeriodicity.lowerMechanicalEventuallyPeriodic"),
                H("Eventual periodicity begins after a finite prefix"),
                StatementSource.FromAuthor(Disp(Seq(
                    Exists, Sp, F.Id("s"), Comma, F.Id("p"), InMacro, Mathbb,
                    Grp(F.Id("N")), Comma, Esc, D(0), Lt, F.Id("p"), Sp, Land, Sp,
                    Forall, Sp, F.Id("n"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    F.Id("w"), Underscore, Grp(Alpha, Comma, Rho),
                    Open, F.Id("s"), Plus, F.Id("n"), Plus, F.Id("p"), Close, Sp, Eq, Sp,
                    F.Id("w"), Underscore, Grp(Alpha, Comma, Rho),
                    Open, F.Id("s"), Plus, F.Id("n"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The definition records a start s, a positive period p, and equality of every "
                    + "letter after shifting the tail by p."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("rational-lower-mechanical-period"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Mechanical/MechanicalPeriodicity.lower_mechanical_word_rat_periodic"),
                H("The reduced denominator is a period for a rational slope"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("r"), InMacro, Mathbb, Grp(F.Id("Q")), Comma, Sp,
                    Forall, Sp, Rho, InMacro, Mathbb, Grp(F.Id("R")), Comma, Esc,
                    Operatorname, Grp(F.Id("Periodic")), Open,
                    F.Id("w"), Underscore, Grp(F.Id("r"), Comma, Rho), Comma,
                    Operatorname, Grp(F.Id("den")), Open, F.Id("r"), Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Shifting an index by the reduced denominator adds the integer numerator to "
                    + "both floor endpoints, so their difference and Boolean readout are unchanged."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("lower-mechanical-periodicity-classifier"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Mechanical/MechanicalPeriodicity.lower_mechanical_eventually_periodic_iff_not_irrational"),
                H("Eventual periodicity is equivalent to rationality of the slope"),
                StatementSource.FromAuthor(Disp(Seq(
                    Neg, Operatorname, Grp(F.Id("Irrational")), Open, Alpha, Close,
                    Sp, Iff, Sp, Exists, Sp, F.Id("s"), Comma, F.Id("p"), InMacro,
                    Mathbb, Grp(F.Id("N")), Comma, Esc, D(0), Lt, F.Id("p"), Sp, Land, Sp,
                    Forall, Sp, F.Id("n"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    F.Id("w"), Underscore, Grp(Alpha, Comma, Rho),
                    Open, F.Id("s"), Plus, F.Id("n"), Plus, F.Id("p"), Close, Sp, Eq, Sp,
                    F.Id("w"), Underscore, Grp(Alpha, Comma, Rho),
                    Open, F.Id("s"), Plus, F.Id("n"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For the reverse implication, periodic block counts grow exactly linearly. "
                    + "The discrepancy bound keeps their difference from length times alpha below "
                    + "one at every multiple, forcing the block count to equal p alpha."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S1/Words/Mechanical/MechanicalDensity")),
        ]));
}
