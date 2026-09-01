using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ZetaObservation;

internal sealed class ChristoffelAtomFloorDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive point mass forces a uniform positive floor on normalized "
            + "polynomial energy and its degree-bounded Christoffel infimum.",
        H("Christoffel Atom Floor"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("christoffel-atom-floor"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/ZetaObservation/ChristoffelAtomFloor."
                        + "christoffel_atom_floor"),
                H("An atom gives every Christoffel cost a positive floor"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The Christoffel evaluation cost is the literal infimum of the "
                            + "extended nonnegative squared-norm integral over complex "
                            + "polynomials whose degree is at most N and whose value at w is "
                            + "one.")),
                    Paragraph(Text(
                        "Restricting the integral to the singleton w gives exactly the atom "
                            + "mass times the squared value there. Monotonicity from the "
                            + "singleton to the whole carrier yields the polynomial bound; "
                            + "taking the infimum yields the same positive floor for every "
                            + "degree."))),
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

    private static Formula TheoremFormula()
    {
        Formula complex = Call("Complex");
        Formula ennreal = Call("ENNReal");
        Formula natural = Call("Nat");
        Formula polynomialType = Call("Polynomial", complex);
        Formula measure = F.Id("mu");
        Formula point = F.Id("w");
        Formula mass = F.Id("m");
        Formula polynomial = F.Id("p");
        Formula degree = F.Id("N");
        Formula z = F.Id("z");
        Formula valueAtPoint = Call("PolynomialEval", polynomial, point);
        Formula pointNorm = Call("ENNRealOfReal", Call("ComplexNormSq", valueAtPoint));
        Formula pointContribution = Call("Product", mass, pointNorm);
        Formula energy = Call(
            "LIntegral",
            measure,
            Lambda(
                z,
                Call(
                    "ENNRealOfReal",
                    Call("ComplexNormSq", Call("PolynomialEval", polynomial, z)))));
        Formula cost = Call("ChristoffelEvaluationCost", measure, point, degree);
        Formula atomHypotheses = And(
            EqualTo(Call("MeasureSingleton", measure, point), mass),
            LessThan(D(0), mass));
        Formula polynomialBound = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("p", polynomialType)],
            Implies(
                EqualTo(valueAtPoint, D(1)),
                And(
                    LessThanOrEqual(pointContribution, energy),
                    EqualTo(pointContribution, mass))));
        Formula degreeFloor = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("N", natural)],
            And(
                LessThanOrEqual(mass, cost),
                LessThan(D(0), cost)));
        Formula conclusion = And(polynomialBound, degreeFloor);

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("mu", Call("Measure", complex)),
                Bound("w", complex),
                Bound("m", ennreal),
            ],
            Implies(atomHypotheses, conclusion)));
    }
}
