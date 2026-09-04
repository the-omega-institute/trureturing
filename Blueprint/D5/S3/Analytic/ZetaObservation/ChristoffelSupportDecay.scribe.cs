using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ZetaObservation;

internal sealed class ChristoffelSupportDecayDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unit-circle support supplies normalized monomial witnesses whose geometric "
            + "energy bound forces exterior Christoffel costs to vanish.",
        H("Christoffel Support Decay"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("christoffel-support-decay"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/ZetaObservation/ChristoffelSupportDecay."
                        + "christoffel_support_decay"),
                H("Unit-circle support forces exterior Christoffel decay"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every degree, the explicit polynomial w inverse to the N, "
                            + "times z to the N, has degree at most N, equals one at w, "
                            + "and has constant norm on the unit circle.")),
                    Paragraph(Text(
                        "Support on that circle identifies its full energy with the circle "
                            + "mass times the squared geometric ratio. This admissible "
                            + "witness bounds the canonical cost, and the ratio is below "
                            + "one because w lies outside the circle."))),
                DescribeRole.Theorem))));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula EqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LessThan(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessThanOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Lambda(Formula binder, Formula body) =>
        Seq(Open, binder, Sp, Mapsto, Sp, body, Close);

    private static Formula Let(
        Formula name,
        Formula domain,
        Formula value,
        Formula body) =>
        Seq(
            Operatorname, Grp(F.Id("let")), Sp,
            name, Colon, Sp, domain, Sp, Colon, Eq, Sp, value, Semi, Sp,
            body);

    private static Formula TheoremFormula()
    {
        Formula complex = Call("Complex");
        Formula ennreal = Call("ENNReal");
        Formula natural = Call("Nat");
        Formula polynomialType = Call("Polynomial", complex);
        Formula measure = F.Id("mu");
        Formula point = F.Id("w");
        Formula degree = F.Id("N");
        Formula witness = F.Id("pN");
        Formula z = F.Id("z");
        Formula unitCircle = Call("sphere", D(0), D(1));
        Formula pointNorm = new Formula.Norm(point);
        Formula inversePoint = Call("inv", point);
        Formula witnessDefinition =
            Call("PolynomialMonomial", degree, Call("pow", inversePoint, degree));
        Formula witnessValue = Call("PolynomialEval", witness, point);
        Formula cost = Call("ChristoffelEvaluationCost", measure, point, degree);
        Formula ratioPower = Call(
            "pow",
            Call("inv", Call("ENNRealOfReal", pointNorm)),
            Multiply(D(2), degree));
        Formula assumptions = And(
            Call("IsFiniteMeasure", measure),
            And(
                LessThan(D(1), pointNorm),
                Call("Subset", Call("MeasureSupport", measure), unitCircle)));
        Formula circleNorm = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("z", complex)],
            Implies(
                Call("Mem", z, unitCircle),
                EqualTo(
                    new Formula.Norm(Call("PolynomialEval", witness, z)),
                    Call("pow", Call("inv", pointNorm), degree))));
        Formula witnessClauses = And(
            LessThanOrEqual(Call("NatDegree", witness), degree),
            And(
                EqualTo(witnessValue, D(1)),
                And(
                    circleNorm,
                    LessThanOrEqual(
                        cost,
                        Multiply(Call("MeasureOf", measure, unitCircle), ratioPower)))));
        Formula everyWitness = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("N", natural)],
            Let(witness, polynomialType, witnessDefinition, witnessClauses));
        Formula costLimit = Call(
            "Tendsto",
            Lambda(degree, cost),
            F.Id("atTop"),
            Call("nhds", D(0)));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("mu", Call("Measure", complex)),
                Bound("w", complex),
            ],
            Implies(assumptions, And(everyWitness, costLimit))));
    }
}
