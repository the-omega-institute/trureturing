using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Adelic;

internal sealed class GlobalLogarithmicGaugeCriterionDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A global analytic logarithm of the shifted completed-zeta reading exists exactly "
            + "when every nontrivial zero lies on the critical line.",
        H("Global Logarithmic Gauge Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("global-logarithmic-gauge-criterion"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Adelic/GlobalLogarithmicGaugeCriterion."
                        + "global_logarithmic_gauge_criterion"),
                H("Global analytic logarithms characterize the critical line"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The displayed rightHalfPlane, shiftedXi, and criticalLineHypothesis "
                            + "are the three literal let-definitions in the Lean theorem. The "
                            + "shift uses the repository's canonical completed-zeta reading.")),
                    Paragraph(Text(
                        "The forward direction constructs the logarithm from a primitive of the "
                            + "logarithmic derivative on the open convex half-plane. The reverse "
                            + "direction uses nonvanishing of the complex exponential together "
                            + "with the canonical completed-zeta zero criterion and reflection.")),
                    Paragraph(Text(
                        "The second conjunct exposes the imaginary real differential of the "
                            + "chosen analytic logarithm and proves it continuous on the whole "
                            + "right half-plane. The final conjunct states both obstructions: a "
                            + "zero rules out the global logarithm and cannot belong to any domain "
                            + "carrying an exponential lift of shiftedXi."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula IffFormula(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula ImpliesFormula(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Member(Formula value, Formula set) =>
        new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);

    private static Formula Lambda(Formula binder, Formula body) =>
        Seq(Open, binder, Sp, Mapsto, Sp, body, Close);

    private static Formula TheoremFormula()
    {
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula proposition = F.Id("Prop");
        Formula complexFunction = Arrow(complex, complex);
        Formula rightHalfPlane = F.Id("rightHalfPlane");
        Formula shiftedXi = F.Id("shiftedXi");
        Formula criticalLineHypothesis = F.Id("criticalLineHypothesis");
        Formula z = F.Id("z");
        Formula s = F.Id("s");
        Formula z0 = F.Id("z0");
        Formula half = new Formula.Fraction(D(1), D(2));

        Formula rightHalfDefinition = new Formula.SetBuilder(
            Seq(D(0), Sp, Lt, Sp, Call("re", z)), z, complex);
        Formula shiftedDefinition = Lambda(
            z,
            Call("xiReading", Seq(half, Sp, Plus, Sp, z)));
        Formula criticalDefinition = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", complex)],
            ImpliesFormula(
                Call("IsNontrivialZero", s),
                Equal(Call("re", s), half)));

        Formula exponentialLift = Lambda(z, Call("exp", Apply(F.Id("L"), z)));
        Formula analyticLog = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("L", complexFunction)],
            And(
                Call("AnalyticOnNhd", complex, F.Id("L"), rightHalfPlane),
                Call("EqOn", exponentialLift, shiftedXi, rightHalfPlane)));
        Formula criterion = IffFormula(criticalLineHypothesis, analyticLog);

        Formula phaseGauge = Lambda(
            z,
            Call(
                "comp",
                F.Id("imCLM"),
                Call(
                    "restrictScalars",
                    real,
                    Call("fderiv", complex, F.Id("L"), z))));
        Formula gaugedLog = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("L", complexFunction)],
            And(
                Call("AnalyticOnNhd", complex, F.Id("L"), rightHalfPlane),
                And(
                    Call("EqOn", exponentialLift, shiftedXi, rightHalfPlane),
                    Call("ContinuousOn", phaseGauge, rightHalfPlane))));
        Formula gaugeClause = ImpliesFormula(criticalLineHypothesis, gaugedLog);

        Formula noGlobalLog = new Formula.Not(analyticLog);
        Formula domain = F.Id("domain");
        Formula localExponentialLift = Lambda(z, Call("exp", Apply(F.Id("L"), z)));
        Formula deleteZero = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("domain", Call("Set", complex)),
                Bound("L", complexFunction),
            ],
            ImpliesFormula(
                Call("EqOn", localExponentialLift, shiftedXi, domain),
                new Formula.Not(Member(z0, domain))));
        Formula zeroObstruction = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("z0", complex)],
            ImpliesFormula(
                And(
                    Member(z0, rightHalfPlane),
                    Equal(Apply(shiftedXi, z0), D(0))),
                And(noGlobalLog, deleteZero)));

        Formula result = And(criterion, And(gaugeClause, zeroObstruction));

        return Disp(new Formula.Aligned([
            Seq(
                rightHalfPlane, Sp, Colon, Sp, Call("Set", complex), Sp, Eq, Sp,
                rightHalfDefinition),
            Seq(
                shiftedXi, Sp, Colon, Sp, complexFunction, Sp, Eq, Sp,
                shiftedDefinition),
            Seq(
                criticalLineHypothesis, Sp, Colon, Sp, proposition, Sp, Eq, Sp,
                criticalDefinition),
            Seq(Open, result, Close, Dot),
        ]));
    }
}
