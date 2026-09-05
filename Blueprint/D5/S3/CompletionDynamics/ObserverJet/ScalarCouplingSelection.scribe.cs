using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CompletionDynamics.ObserverJet;

internal sealed class ScalarCouplingSelectionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/CompletionDynamics/ObserverJet/ScalarCouplingSelection.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rotation and reflection invariance force every second-order scalar regulator mode to be radial.",
        H("Scalar Coupling Selection"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("invariant-second-order-mode-is-radial"),
                DeclarationHandle.Create(Prefix + "invariant_second_order_mode_is_radial"),
                H("Invariant second-order modes are radial"),
                StatementSource.FromAuthor(RadialClassificationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The displayed secondOrderMode is the general real degree-at-most-two "
                            + "polynomial in a two-coordinate regulator mode, with the constant "
                            + "term kept outside the mode. Invariance under every standard plane "
                            + "rotation and the generating reflection removes both linear "
                            + "coefficients and the mixed quadratic coefficient, and equates the "
                            + "two diagonal quadratic coefficients."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("scalar-coupling-selection-rule"),
                DeclarationHandle.Create(Prefix + "scalar_coupling_selection_rule"),
                H("Completed scalar coupling begins quadratically"),
                StatementSource.FromAuthor(SelectionRuleFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every positive-indexed family of second-order regulator modes and "
                            + "higher invariant remainders, the completed and higher terms are "
                            + "assumed invariant under all standard rotations and under the "
                            + "generating reflection. The modal contribution then reduces "
                            + "termwise to kappa(n) times the squared regulator norm, with the "
                            + "arbitrary higher invariant retained.")),
                    Paragraph(Text(
                        "For every nonzero real displacement delta and every real height gamma, "
                            + "the explicitly displayed reflected complex pair has center "
                            + "one-half plus i gamma, zero signed first moment, second moment "
                            + "delta squared, and strictly positive second moment."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/CompletionDynamics/ObserverJet/PairedOddJetCancellation")),
        ]));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Call(string name, params Formula[] arguments)
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

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula ForallFormula(Formula.BoundVariable[] binders, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. binders], body);

    private static Formula ExistsFormula(Formula.BoundVariable[] binders, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. binders], body);

    private static Formula PowTwo(Formula value) =>
        new Formula.Power(value, D(2));

    private static Formula Tsum(Formula binder, Formula type, Formula body) =>
        Seq(SigmaLower, Underscore, Grp(binder, Colon, Sp, type), Sp, body);

    private static Formula Mode(
        Formula linearX,
        Formula linearY,
        Formula quadraticXX,
        Formula quadraticXY,
        Formula quadraticYY,
        Formula u) =>
        Call("secondOrderMode", linearX, linearY, quadraticXX, quadraticXY, quadraticYY, u);

    private static Formula RadialClassificationFormula()
    {
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula regulatorMode = F.Id("RegulatorMode");
        Formula linearX = F.Id("linearX");
        Formula linearY = F.Id("linearY");
        Formula quadraticXX = F.Id("quadraticXX");
        Formula quadraticXY = F.Id("quadraticXY");
        Formula quadraticYY = F.Id("quadraticYY");
        Formula theta = F.Id("theta");
        Formula u = F.Id("u");
        Formula modeAt(Formula point) =>
            Mode(linearX, linearY, quadraticXX, quadraticXY, quadraticYY, point);

        Formula rotation = ForallFormula(
            [Bound("theta", real), Bound("u", regulatorMode)],
            Equal(modeAt(Call("regulatorRotation", theta, u)), modeAt(u)));
        Formula reflection = ForallFormula(
            [Bound("u", regulatorMode)],
            Equal(modeAt(Call("regulatorReflection", u)), modeAt(u)));
        Formula conclusion = ForallFormula(
            [Bound("u", regulatorMode)],
            Equal(
                modeAt(u),
                Seq(quadraticXX, Sp, Times, Sp, PowTwo(new Formula.Norm(u)))));

        Formula result = ForallFormula(
            [
                Bound("linearX", real),
                Bound("linearY", real),
                Bound("quadraticXX", real),
                Bound("quadraticXY", real),
                Bound("quadraticYY", real),
            ],
            Implies(And(rotation, reflection), conclusion));
        return Disp(Seq(result, Dot));
    }

    private static Formula SelectionRuleFormula()
    {
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula positiveNaturals = Seq(Operatorname, Grp(F.Id("PNat")));
        Formula regulatorMode = F.Id("RegulatorMode");
        Formula coefficientFamily = Arrow(positiveNaturals, real);
        Formula modeFamily = Arrow(positiveNaturals, regulatorMode);
        Formula higherFamily = Arrow(positiveNaturals, Arrow(regulatorMode, real));
        Formula f0 = F.Id("F0");
        Formula linearX = F.Id("linearX");
        Formula linearY = F.Id("linearY");
        Formula quadraticXX = F.Id("quadraticXX");
        Formula quadraticXY = F.Id("quadraticXY");
        Formula quadraticYY = F.Id("quadraticYY");
        Formula higher = F.Id("higherInvariant");
        Formula n = F.Id("n");
        Formula theta = F.Id("theta");
        Formula u = F.Id("u");
        Formula delta = F.Id("delta");
        Formula gamma = F.Id("gamma");
        Formula kappa = F.Id("kappa");
        Formula modes = F.Id("modes");
        Formula coefficient(Formula family) => Apply(family, n);
        Formula higherAt(Formula point) => Apply(Apply(higher, n), point);
        Formula modeAt(Formula point) => Mode(
            coefficient(linearX),
            coefficient(linearY),
            coefficient(quadraticXX),
            coefficient(quadraticXY),
            coefficient(quadraticYY),
            point);

        Formula rotated = Call("regulatorRotation", theta, u);
        Formula reflected = Call("regulatorReflection", u);
        Formula completedRotation = ForallFormula(
            [Bound("n", positiveNaturals), Bound("theta", real), Bound("u", regulatorMode)],
            Equal(
                Seq(modeAt(rotated), Sp, Plus, Sp, higherAt(rotated)),
                Seq(modeAt(u), Sp, Plus, Sp, higherAt(u))));
        Formula higherRotation = ForallFormula(
            [Bound("n", positiveNaturals), Bound("theta", real), Bound("u", regulatorMode)],
            Equal(higherAt(rotated), higherAt(u)));
        Formula completedReflection = ForallFormula(
            [Bound("n", positiveNaturals), Bound("u", regulatorMode)],
            Equal(
                Seq(modeAt(reflected), Sp, Plus, Sp, higherAt(reflected)),
                Seq(modeAt(u), Sp, Plus, Sp, higherAt(u))));
        Formula higherReflection = ForallFormula(
            [Bound("n", positiveNaturals), Bound("u", regulatorMode)],
            Equal(higherAt(reflected), higherAt(u)));
        Formula nonzeroDelta = new Formula.Relation(
            delta, FormulaRelationOperator.NotEqual, D(0));
        Formula premises = And(
            completedRotation,
            And(
                higherRotation,
                And(completedReflection, And(higherReflection, nonzeroDelta))));

        Formula modeN = Apply(modes, n);
        Formula originalSummand = Seq(
            modeAt(modeN), Sp, Plus, Sp, higherAt(modeN));
        Formula radialSummand = Seq(
            Apply(kappa, n), Sp, Times, Sp, PowTwo(new Formula.Norm(modeN)),
            Sp, Plus, Sp, higherAt(modeN));
        Formula modalReduction = ForallFormula(
            [Bound("modes", modeFamily)],
            Equal(
                Seq(f0, Sp, Plus, Sp, Tsum(n, positiveNaturals, Grp(originalSummand))),
                Seq(f0, Sp, Plus, Sp, Tsum(n, positiveNaturals, Grp(radialSummand)))));

        Formula half = new Formula.Fraction(D(1), D(2));
        Formula right = F.Id("right");
        Formula left = F.Id("left");
        Formula center = F.Id("center");
        Formula imaginaryHeight = Seq(F.Id("i"), Sp, Times, Sp, gamma);
        Formula rightDefinition = Seq(half, Sp, Plus, Sp, delta, Sp, Plus, Sp, imaginaryHeight);
        Formula leftDefinition = Seq(half, Sp, Minus, delta, Sp, Plus, Sp, imaginaryHeight);
        Formula centerDefinition = Seq(half, Sp, Plus, Sp, imaginaryHeight);
        Formula barycenter = Equal(
            new Formula.Fraction(Seq(right, Sp, Plus, Sp, left), D(2)),
            center);
        Formula firstMoment = Equal(
            new Formula.Fraction(Seq(delta, Sp, Plus, Sp, Grp(Minus, delta)), D(2)),
            D(0));
        Formula secondMomentValue = new Formula.Fraction(
            Seq(PowTwo(delta), Sp, Plus, Sp, PowTwo(Grp(Minus, delta))), D(2));
        Formula secondMoment = Equal(secondMomentValue, PowTwo(delta));
        Formula positiveSecondMoment = new Formula.Relation(
            D(0), FormulaRelationOperator.LessThan, secondMomentValue);
        Formula reflectedPair = Seq(
            Operatorname, Grp(F.Id("let")), Sp,
            right, Colon, Sp, complex, Sp, Colon, Eq, Sp, rightDefinition, Semi, Sp,
            Operatorname, Grp(F.Id("let")), Sp,
            left, Colon, Sp, complex, Sp, Colon, Eq, Sp, leftDefinition, Semi, RowBreak, Grp(),
            Operatorname, Grp(F.Id("let")), Sp,
            center, Colon, Sp, complex, Sp, Colon, Eq, Sp, centerDefinition, Semi, Sp,
            And(barycenter, And(firstMoment, And(secondMoment, positiveSecondMoment))));
        Formula conclusion = ExistsFormula(
            [Bound("kappa", coefficientFamily)],
            And(modalReduction, reflectedPair));
        Formula result = ForallFormula(
            [
                Bound("F0", real),
                Bound("linearX", coefficientFamily),
                Bound("linearY", coefficientFamily),
                Bound("quadraticXX", coefficientFamily),
                Bound("quadraticXY", coefficientFamily),
                Bound("quadraticYY", coefficientFamily),
                Bound("higherInvariant", higherFamily),
                Bound("delta", real),
                Bound("gamma", real),
            ],
            Implies(premises, conclusion));

        return Disp(Seq(result, Dot));
    }
}
