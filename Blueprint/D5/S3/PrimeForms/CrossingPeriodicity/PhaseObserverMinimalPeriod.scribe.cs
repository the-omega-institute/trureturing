using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms.CrossingPeriodicity;

internal sealed class PhaseObserverMinimalPeriodDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The named winding-phase observer has least positive translation period "
            + "m divided by gcd(m,2), with the six-step modulus-twelve case.",
        H("Minimal Period of the Phase Observer"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("phase-observer-modulo-a-natural-modulus"),
                DeclarationHandle.Create(
                    "D5/S3/PrimeForms/CrossingPeriodicity/PhaseObserverMinimalPeriod."
                        + "phaseObserver"),
                H("The phase observer modulo a natural modulus"),
                StatementSource.FromAuthor(ObserverFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The source symbol Psi is the existing windingPhase. Since that phase is "
                        + "rational, reduction modulo the natural m is represented by the "
                        + "existing rational additive circle of period m."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("closed-form-phase-period"),
                DeclarationHandle.Create(
                    "D5/S3/PrimeForms/CrossingPeriodicity/PhaseObserverMinimalPeriod."
                        + "phasePeriod"),
                H("The closed-form phase period"),
                StatementSource.FromAuthor(PeriodFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The period function is defined on natural moduli by dividing m by its "
                        + "greatest common divisor with the translation step two."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("phase-period-is-the-least-positive-return-time"),
                DeclarationHandle.Create(
                    "D5/S3/PrimeForms/CrossingPeriodicity/PhaseObserverMinimalPeriod."
                        + "phase_period_eq"),
                H("The phase period is the least positive return time"),
                StatementSource.FromAuthor(MinimalPeriodFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For positive m, Mathlib's exact additive-order formula for two in ZMod m "
                        + "gives T(m). Its minimal-order characterization proves both return "
                        + "and exclusion of every smaller positive step count."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("additive-circle-period-agrees-with-the-closed-form"),
                DeclarationHandle.Create(
                    "D5/S3/PrimeForms/CrossingPeriodicity/PhaseObserverMinimalPeriod."
                        + "phase_period_addCircle_eq"),
                H("The additive-circle period agrees with the closed form"),
                StatementSource.FromAuthor(AddCirclePeriodFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The imported observer evolves by translation by minus two on AddCircle m. "
                        + "Mathlib's gcd-times-order identity proves that this step has the same "
                        + "order T(m), so the ZMod calculation and the existing model agree."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("positive-modulus-is-necessary"),
                DeclarationHandle.Create(
                    "D5/S3/PrimeForms/CrossingPeriodicity/PhaseObserverMinimalPeriod."
                        + "positive_modulus_is_necessary"),
                H("A positive modulus is necessary"),
                StatementSource.FromAuthor(ZeroModulusFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At m=0 the closed form is zero. The additive-order convention also reports "
                        + "zero for the infinite-order translation in ZMod 0, but zero cannot be "
                        + "a least positive period, so positivity is a necessary hypothesis."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("six-step-period-from-four-and-three"),
                DeclarationHandle.Create(
                    "D5/S3/PrimeForms/CrossingPeriodicity/PhaseObserverMinimalPeriod."
                        + "phase_period_twelve"),
                H("The modulus-twelve period is six"),
                StatementSource.FromAuthor(TwelveFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The fixed calculation records the source's coprime factors four and three, "
                        + "their periods two and three, and the resulting least common multiple "
                        + "six. It checks the CRT path numerically rather than proving a general "
                        + "CRT theorem for arbitrary moduli."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/PrimeForms/CrossingPeriodicity/SandwichPhasePeriod")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/PrimeForms/CrossingPeriodicity/PhaseObserverTranslation")),
        ]));

    private static Formula PeriodAt(Formula modulus) =>
        Seq(F.Id("T"), Open, modulus, Close);

    private static Formula OrderAt(Formula modulus) =>
        Seq(Operatorname, Grp(F.Id("ord")), Underscore, Grp(modulus));

    private static Formula ObserverFormula()
    {
        Formula modulus = F.Id("m");
        Formula matrix = F.Id("A");
        Formula observer = Seq(F.Id("q"), Underscore, Grp(modulus));
        Formula phase = Seq(Operatorname, Grp(F.Id("Psi")));

        return Disp(Seq(
            observer, Open, matrix, Close, Eq,
            OpenBracket, phase, Open, matrix, Close, CloseBracket,
            Underscore, Grp(modulus), Dot));
    }

    private static Formula PeriodFormula()
    {
        Formula modulus = F.Id("m");
        Formula gcd = Seq(Operatorname, Grp(F.Id("gcd")),
            Open, modulus, Comma, Sp, D(2), Close);

        return Disp(Seq(
            PeriodAt(modulus), Eq, Frac, Grp(modulus), Grp(gcd), Dot));
    }

    private static Formula MinimalPeriodFormula()
    {
        Formula modulus = F.Id("m");
        Formula step = Grp(Minus, D(2));
        Formula period = PeriodAt(modulus);
        Formula order = OrderAt(modulus);
        Formula count = F.Id("k");

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, modulus, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                D(0), Lt, modulus, Sp, Rightarrow, Sp,
                order, Open, step, Close, Eq, period, Sp, Land, Sp, D(0), Lt, period),
            Seq(
                period, Cdot, step, Eq, D(0), Comma, Sp,
                Forall, Sp, count, Comma, Sp,
                D(0), Lt, count, Lt, period, Sp, Rightarrow, Sp,
                count, Cdot, step, Neq, D(0), Dot),
        ]));
    }

    private static Formula AddCirclePeriodFormula()
    {
        Formula modulus = F.Id("m");
        Formula circle = Seq(Operatorname, Grp(F.Id("AddCircle")), Open, modulus, Close);

        return Disp(Seq(
            D(0), Lt, modulus, Sp, Rightarrow, Sp,
            Seq(Operatorname, Grp(F.Id("ord")), Underscore, Grp(circle)),
            Open, Minus, D(2), Close, Eq, PeriodAt(modulus), Sp, Land, Sp,
            D(0), Lt, PeriodAt(modulus), Dot));
    }

    private static Formula ZeroModulusFormula()
    {
        Formula zeroPeriod = PeriodAt(D(0));
        Formula zeroOrder = OrderAt(D(0));

        return Disp(Seq(
            Neg, Grp(
                D(0), Lt, zeroPeriod, Sp, Land, Sp,
                zeroOrder, Open, Minus, D(2), Close, Eq, zeroPeriod), Dot));
    }

    private static Formula TwelveFormula() => Disp(new Formula.Aligned([
        Seq(D(1, 2), Eq, D(4), Cdot, D(3), Comma),
        Seq(PeriodAt(D(4)), Eq, D(2), Comma, Sp, PeriodAt(D(3)), Eq, D(3), Comma),
        Seq(
            PeriodAt(D(1, 2)), Eq,
            Operatorname, Grp(F.Id("lcm")), Open, D(2), Comma, Sp, D(3), Close,
            Eq, D(6), Dot),
    ]));
}
