using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Midline.Cayley;

internal sealed class RadialBoundaryPhaseDerivativeDocument : IScribeDocumentDefinition
{
    private const string Handle =
        "D5/S3/Midline/Cayley/RadialBoundaryPhaseDerivative."
            + "radial_boundary_phase_derivative";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normal logarithmic Cayley radius and its smooth boundary phase have the "
            + "same Poisson-kernel derivative.",
        H("Radial Boundary Phase Derivative"),
        Blocks(Describe.Lean(
            DescribeId.Create("radial-boundary-phase-derivative"),
            DeclarationHandle.Create(Handle),
            H("Radial and boundary phase derivatives coincide"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For a positive scale, the off-axis Cayley coordinate is constructed "
                        + "from the real tangential and normal coordinates. Its logarithmic "
                        + "norm is the radial coordinate, while pi minus twice the arctangent "
                        + "is a smooth real phase lift of the boundary value.")),
                Paragraph(Text(
                    "The exponential clause ties that lift to the canonical boundary Cayley "
                        + "point, including the branch-cut point. The norm clauses state that "
                        + "the coordinate is unitary exactly when the normal displacement "
                        + "vanishes.")),
                Paragraph(Text(
                    "Both derivative clauses use the same explicitly constructed Poisson "
                        + "kernel value. Thus the normal derivative of the logarithmic radius "
                        + "is the tangential derivative of the boundary phase."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula real = Call("Real");
        Formula complex = Call("Complex");
        Formula a = F.Id("a");
        Formula gamma = F.Id("gamma");
        Formula delta = F.Id("delta");
        Formula cayleyCoordinate = F.Id("cayleyCoordinate");
        Formula radialCoordinate = F.Id("radialCoordinate");
        Formula boundaryPhase = F.Id("boundaryPhase");
        Formula poissonKernel = F.Id("poissonKernel");
        Formula imaginaryUnit = Seq(F.Id("Complex"), Dot, F.Id("I"));
        Formula pi = Seq(F.Id("Real"), Dot, F.Id("pi"));

        Formula complexGamma = Call("complex", gamma);
        Formula complexDelta = Call("complex", delta);
        Formula complexA = Call("complex", a);
        Formula shifted = Sub(complexGamma, Mul(imaginaryUnit, complexDelta));
        Formula cayleyValue = Div(
            Add(shifted, Mul(imaginaryUnit, complexA)),
            Sub(shifted, Mul(imaginaryUnit, complexA)));
        Formula radialValue = Call(
            "log",
            Norm(Apply(cayleyCoordinate, gamma, delta)));
        Formula phaseValue = Sub(
            pi,
            Mul(D(2), Call("arctan", Div(gamma, a))));
        Formula poissonValue = Call(
            "RiemannPoissonDensityPoissonKernel",
            a,
            gamma);
        Formula commonDerivative =
            Mul(Mul(Seq(Minus, D(2)), pi), Apply(poissonKernel, gamma));

        Formula phaseRepresentation = Equal(
            Call(
                "complex",
                Apply(Seq(F.Id("Circle"), Dot, F.Id("exp")),
                    Apply(boundaryPhase, gamma))),
            Apply(cayleyCoordinate, gamma, D(0)));
        Formula axisNorm = Equal(
            Norm(Apply(cayleyCoordinate, gamma, D(0))),
            D(1));
        Formula offAxisNorm = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("delta", real)],
            Implies(
                NotEqual(delta, D(0)),
                NotEqual(Norm(Apply(cayleyCoordinate, gamma, delta)), D(1))));
        Formula radialDerivative = Call(
            "HasDerivAt",
            Lambda("delta", real, Apply(radialCoordinate, gamma, delta)),
            commonDerivative,
            D(0));
        Formula phaseDerivative = Call(
            "HasDerivAt",
            boundaryPhase,
            commonDerivative,
            gamma);
        Formula conclusion = And(
            phaseRepresentation,
            And(
                axisNorm,
                And(
                    offAxisNorm,
                    And(radialDerivative, phaseDerivative))));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, a, Comma, Sp, gamma, Colon, Sp, real, Comma,
            RowBreak, Grp(),
            Less(D(0), a), Sp, Rightarrow,
            RowBreak, Grp(),
            Let(
                cayleyCoordinate,
                Arrow(real, Arrow(real, complex)),
                Lambda2("gamma", "delta", real, cayleyValue)),
            RowBreak, Grp(),
            Let(
                radialCoordinate,
                Arrow(real, Arrow(real, real)),
                Lambda2("gamma", "delta", real, radialValue)),
            RowBreak, Grp(),
            Let(
                boundaryPhase,
                Arrow(real, real),
                Lambda("gamma", real, phaseValue)),
            RowBreak, Grp(),
            Let(
                poissonKernel,
                Arrow(real, real),
                Lambda("gamma", real, poissonValue)),
            RowBreak, Grp(),
            conclusion, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Let(Formula name, Formula type, Formula value) =>
        Seq(
            Operatorname, Grp(F.Id("let")), Sp,
            name, Colon, Sp, type, Sp, Colon, Eq, Sp, value, Comma);

    private static Formula Lambda(string name, Formula type, Formula body) =>
        Lambda(F.Id(name), type, body);

    private static Formula Lambda(Formula binder, Formula type, Formula body) =>
        Seq(Open, binder, Colon, Sp, type, Sp, Mapsto, Sp, body, Close);

    private static Formula Lambda2(
        string first,
        string second,
        Formula type,
        Formula body) =>
        Seq(
            Open,
            F.Id(first), Colon, Sp, type, Comma, Sp,
            F.Id(second), Colon, Sp, type,
            Sp, Mapsto, Sp, body,
            Close);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Arrow(Formula source, Formula target) =>
        new Formula.TypeArrow(source, target);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Div(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);

    private static Formula Norm(Formula value) =>
        new Formula.Norm(value);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
}
