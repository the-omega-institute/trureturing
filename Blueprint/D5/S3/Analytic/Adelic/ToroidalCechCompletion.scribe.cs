using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Adelic;

internal sealed class ToroidalCechCompletionDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Quadratic-period ratios agree on overlaps and glue uniquely to the completed-zeta "
            + "amplitude.",
        H("Toroidal Cech Completion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("toroidal-cech-completion"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Adelic/ToroidalCechCompletion."
                        + "toroidal_cech_completion"),
                H("Quadratic-period charts glue uniquely to xi"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Each chart is constructed as the nonvanishing domain of one twist. "
                            + "Continuity of the period and twist constructs the local "
                            + "period-over-twist map on that exact subtype.")),
                    Paragraph(Text(
                        "The displayed factorization identifies every local ratio with the "
                            + "repository's canonical entire xi reading. The pointwise "
                            + "nonvanishing hypothesis says these charts cover Omega.")),
                    Paragraph(Text(
                        "The frozen continuous local-factor gluing theorem supplies overlap "
                            + "compatibility and the unique continuous glue. Its computation "
                            + "rule identifies that glue with restrictedXi on every chart."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new Formula.BoundVariable(FormulaIdentifier.Create(name), domain);

    private static Formula EqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula TheoremFormula()
    {
        Formula type = Call("Type");
        Formula complex = Call("Complex");
        Formula indexType = F.Id("Index");
        Formula omega = F.Id("Omega");
        Formula period = F.Id("P");
        Formula twist = F.Id("T");
        Formula first = F.Id("i");
        Formula second = F.Id("j");
        Formula point = F.Id("s");
        Formula candidate = F.Id("g");
        Formula functionFamily = Arrow(indexType, Arrow(complex, complex));
        Formula omegaType = Call("Set", complex);
        Formula omegaSubtype = Call("Subtype", omega);
        Formula periodAtFirst = Apply(Apply(period, first), point);
        Formula twistAtFirst = Apply(Apply(twist, first), point);
        Formula twistAtSecond = Apply(Apply(twist, second), point);
        Formula xiAtPoint = Apply(F.Id("xiReading"), point);
        Formula firstDomain = Call("nonvanishingDomain", omega, twist, first);
        Formula secondDomain = Call("nonvanishingDomain", omega, twist, second);
        Formula firstRatio = Call(
            "localPeriodRatio", omega, period, twist, first, point);
        Formula secondRatio = Call(
            "localPeriodRatio", omega, period, twist, second, point);
        Formula restrictedXi = Call("restrictedXi", omega);
        Formula candidateType = Call("ContinuousMap", omegaSubtype, complex);

        Formula periodContinuity = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("i", indexType)],
            Call("Continuous", Apply(period, first)));
        Formula twistContinuity = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("i", indexType)],
            Call("Continuous", Apply(twist, first)));
        Formula factorization = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("i", indexType), Bound("s", complex)],
            EqualTo(periodAtFirst, Seq(xiAtPoint, Sp, Times, Sp, twistAtFirst)));
        Formula cover = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", complex)],
            Implies(
                Call("mem", point, omega),
                new Formula.BindMany(
                    FormulaQuantifier.Exists,
                    [Bound("i", indexType)],
                    NotEqual(twistAtFirst, D(0)))));
        Formula premises = And(
            periodContinuity,
            And(twistContinuity, And(factorization, cover)));

        Formula overlap = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("i", indexType), Bound("j", indexType), Bound("s", omegaSubtype)],
            Implies(
                And(
                    Call("mem", point, firstDomain),
                    Call("mem", point, secondDomain)),
                EqualTo(firstRatio, secondRatio)));
        Formula canonicalRestriction = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("i", indexType), Bound("s", omegaSubtype)],
            Implies(
                Call("mem", point, firstDomain),
                EqualTo(xiAtPoint, firstRatio)));
        Formula candidateRestriction = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("i", indexType), Bound("s", omegaSubtype)],
            Implies(
                Call("mem", point, firstDomain),
                EqualTo(Apply(candidate, point), firstRatio)));
        Formula uniqueness = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("g", candidateType)],
            Implies(candidateRestriction, EqualTo(candidate, restrictedXi)));
        Formula conclusion = And(overlap, And(canonicalRestriction, uniqueness));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("Index", type),
                Bound("Omega", omegaType),
                Bound("P", functionFamily),
                Bound("T", functionFamily),
            ],
            Implies(premises, conclusion)));
    }
}
