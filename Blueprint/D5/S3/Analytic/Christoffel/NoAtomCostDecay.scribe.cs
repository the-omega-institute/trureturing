using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Christoffel;

internal sealed class NoAtomCostDecayDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/Christoffel/NoAtomCostDecay.no_atom_cost_decay";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unit-circle support gives an explicit polynomial witness and an exponential "
            + "upper bound for the Christoffel evaluation cost.",
        H("No-Atom Christoffel Cost Decay"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("no-atom-cost-decay"),
                DeclarationHandle.Create(Declaration),
                H("The exterior Christoffel cost decays to zero"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let the Cayley-zero data contain the repository's nontrivial zeta-zero "
                            + "family, a scale a greater than one half, and positive real weights "
                            + "that are invariant under reflection and conjugation, absolutely "
                            + "summable, and normalized to sum to one. Let muA be their named "
                            + "weighted Dirac sum after the shifted zeros pass through the source "
                            + "Cayley map. Assume its support is contained in the unit circle and "
                            + "let w have norm greater than one.")),
                    Paragraph(Text(
                        "Its value at w is one and its norm on the unit circle is the Nth "
                            + "power of the inverse norm of w. The same polynomial is an "
                            + "admissible witness in the repository's existing Christoffel "
                            + "evaluation-cost infimum.")),
                    Paragraph(Text(
                        "Consequently the cost is nonnegative, is bounded above by the "
                            + "unit-circle mass times the displayed inverse-norm power, and "
                            + "tends to zero. In the source volume the support premise for "
                            + "muA is equivalent to RH. Finiteness follows from normalization, so "
                            + "this declaration is conditional on support, does not add a "
                            + "generic finite-measure premise, and does not assert RH."))),
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

    private static Formula MemberOf(Formula value, Formula set) =>
        new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);

    private static Formula SubsetOf(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.SubsetOf, right);

    private static Formula ForEveryN(Formula body) =>
        new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("N", Call("Nat"))],
            body);

    private static Formula TheoremFormula()
    {
        Formula complex = Call("Complex");
        Formula natural = Call("Nat");
        Formula cayleyData = F.Id("cayleyZeros");
        Formula measure = Call("CayleyZeroMeasure", cayleyData);
        Formula point = F.Id("w");
        Formula degree = F.Id("N");
        Formula z = F.Id("z");
        Formula circle = Call("ComplexUnitCircle");
        Formula pointNorm = Call("ComplexNorm", point);
        Formula inverseNorm = Call("Inverse", pointNorm);
        Formula polynomial = Call("ObservationPolynomial", point, degree);
        Formula evaluationAtPoint = Call("PolynomialEval", polynomial, point);
        Formula evaluationAtZ = Call("PolynomialEval", polynomial, z);
        Formula cost = Call("ChristoffelEvaluationCost", measure, point, degree);
        Formula mass = Call("MeasureOf", measure, circle);
        Formula upperPower = Call(
            "ENNRealOfReal",
            new Formula.Power(
                inverseNorm,
                Call("Product", degree, F.D(2))));

        Formula hypotheses = And(
            SubsetOf(Call("MeasureSupport", measure), circle),
            LessThan(F.D(1), pointNorm));
        Formula centerValue = ForEveryN(EqualTo(evaluationAtPoint, F.D(1)));
        Formula circleNorm = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("N", natural), Bound("z", complex)],
            Implies(
                MemberOf(z, circle),
                EqualTo(
                    Call("ComplexNorm", evaluationAtZ),
                    new Formula.Power(inverseNorm, degree))));
        Formula nonnegativeCost = ForEveryN(LessThanOrEqual(F.D(0), cost));
        Formula exponentialBound = ForEveryN(
            LessThanOrEqual(cost, Call("Product", mass, upperPower)));
        Formula costTendsToZero = Call(
            "Tendsto",
            Call("LambdaNat", F.Id("N"), cost),
            Call("atTop", natural),
            Call("nhds", F.D(0)));
        Formula conclusions = And(
            centerValue,
            And(
                circleNorm,
                And(nonnegativeCost, And(exponentialBound, costTendsToZero))));

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("cayleyZeros", Call("CayleyZeroMeasureData")), Bound("w", complex)],
            Implies(hypotheses, conclusions)));
    }
}
