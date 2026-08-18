using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms.CrossingPeriodicity;

internal sealed class SandwichPhasePeriodDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The sandwich winding phase falls by two each step and first returns modulo twelve "
            + "after exactly six steps.",
        H("Sandwich Phase Period"),
        Blocks(
            Paragraph(Text(
                "The crossing sandwich lowers the winding phase by exactly two at every step. "
                    + "That displacement law is the content of the exact propagation theorem, "
                    + "reached here through its three public consequences rather than through "
                    + "the private lemmas of the orbit module, whose declaration set is frozen.")),
            Paragraph(Text(
                "What follows from a constant drop of two is a period, not merely a drift: "
                    + "twelve is the sixth multiple of two, so the phase returns to its residue "
                    + "modulo twelve after six steps and after no smaller positive number of "
                    + "steps. The orbit module proves only that the orbit meets phase zero once; "
                    + "the periodicity is stated here for the first time.")),
            Paragraph(Text(
                "The minimality half is what carries the word period. Without it the statement "
                    + "would be satisfied by every multiple of six and would assert only that "
                    + "six steps suffice, which a constant drop makes automatic.")),
            Describe.Lean(
                DescribeId.Create("sandwich-phase-first-returns-modulo-twelve-at-six"),
                DeclarationHandle.Create(
                    "D5/S3/PrimeForms/CrossingPeriodicity/SandwichPhasePeriod."
                        + "sandwich_phase_period_package"),
                H("The sandwich phase first returns modulo twelve at six"),
                StatementSource.FromAuthor(PeriodFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The displayed conjunct is the return law; the package also carries the "
                        + "single-step drop and the exclusion of every smaller positive period."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/PrimeForms/Crossing/WindingOrbitZero")),
        ]));

    // D() takes individual decimal digits, not a value: D(12) is the byte 12 and is
    // rejected at emit time by Formula.LatexDigits. Twelve is written D(1, 2).
    private static Formula Iterate(Formula exponent, Formula state) =>
        Seq(F.Id("sigma"), Caret, Grp(exponent), Open, state, Close);

    private static Formula Phase(Formula state) =>
        Seq(Operatorname, Grp(F.Id("Psi")), Open, state, Close);

    private static Formula PeriodFormula()
    {
        Formula matrix = F.Id("A");
        Formula step = F.Id("n");

        return Disp(Seq(
            Forall, Sp, step, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
            Phase(Iterate(Seq(step, Plus, D(6)), matrix)), Sp, Eq, Sp,
            Phase(Iterate(step, matrix)), Sp, Minus, Sp, D(1, 2), Dot));
    }
}
