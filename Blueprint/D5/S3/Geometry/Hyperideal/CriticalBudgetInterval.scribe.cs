using System;
using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class CriticalBudgetIntervalDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Geometry/Hyperideal/CriticalBudgetInterval.exact_budget_interval";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact opposite-edge floor for the prescribed four-plus-two critical angle budget.",
        H("The four-plus-two budget interval"),
        Blocks(
            Paragraph(Text("Let q=49/sqrt(6534), beta=arccos(q), and "
                + "aStar=(25-33sqrt((1-q)/2))/8. The target edge has upper "
                + "cosine-length bound 2; high neighbours have bound 5/4. "
                + "The parameter a is the floor on a favourable opposite edge, "
                + "restricted to 1<a<7/5.")),
            Describe.Lean(
                DescribeId.Create("critical-four-plus-two-budget-interval"),
                DeclarationHandle.Create(Declaration),
                H("The endpoint cosine and exact strict interval"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("At target value 2, four neighbours at 5/4 and "
                        + "opposite value a, the original six-coordinate cosine equals "
                        + "(25-8a)/33. This is the favourable upper-face endpoint, "
                        + "with no cosine value supplied as a premise.")),
                    Paragraph(Text("The prescribed lower budget is "
                        + "2pi-6arccos(2(2-a)/(a+1)); the upper budget is "
                        + "4arccos of the original favourable cosine, plus "
                        + "2beta-2pi. The endpoint equality rewrites it as "
                        + "4arccos((25-8a)/33)+2beta-2pi. Within 1<a<7/5 "
                        + "both are strictly positive exactly when aStar<a. "
                        + "The displayed upper endpoint is in (0,1), so the "
                        + "double-angle identity and strict decrease of cosine on "
                        + "[0,pi] give the threshold without decimal estimates.")),
                    Paragraph(Text("The theorem identifies strictness of this specified "
                        + "analytic budget. It does not assert that a global length "
                        + "vector attains every endpoint or that a geometric "
                        + "realization exists."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var a = F.Id("a");
        var pi = F.Pi;
        var upperCosine = new Formula.Fraction(
            F.Seq(F.D(2, 5), F.Minus, Mul(F.D(8), a)), F.D(3, 3));
        var originalCosine = Call("cosine", F.D(2), Rat(5, 4), Rat(5, 4),
            a, Rat(5, 4), Rat(5, 4));
        var lowerCosine = new Formula.Fraction(
            Mul(F.D(2), F.Seq(F.Open, F.D(2), F.Minus, a, F.Close)),
            F.Seq(a, F.Plus, F.D(1)));
        var lowerBudget = F.Seq(Mul(F.D(2), pi), F.Minus,
            Mul(F.D(6), Call("arccos", lowerCosine)));
        var upperBudget = F.Seq(Mul(F.D(4), Call("arccos", originalCosine)),
            F.Plus, Mul(F.D(2), F.Beta), F.Minus, Mul(F.D(2), pi));
        var strictBudgets = And(Lt(F.D(0), lowerBudget), Lt(F.D(0), upperBudget));
        var exactInterval = And(Lt(F.Id("oppositeThreshold"), a), Lt(a, Rat(7, 5)));
        var result = And(Equal(originalCosine, upperCosine),
            new Formula.Logic(strictBudgets, FormulaLogicOperator.Iff, exactInterval));
        return All([("a", F.Id("Real"))],
            new Formula.Logic(And(Lt(F.D(1), a), Lt(a, Rat(7, 5))),
                FormulaLogicOperator.Implies, result));
    }

    private static Formula All((string Name, Formula Type)[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [.. variables.Select(v => new Formula.BoundVariable(
                FormulaIdentifier.Create(v.Name), v.Type))], body);
    private static Formula And(params Formula[] parts)
    {
        if (parts.Length == 0) throw new ArgumentException("Empty conjunction");
        var result = parts[^1];
        for (var i = parts.Length - 2; i >= 0; i--)
            result = new Formula.Logic(parts[i], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Rat(int numerator, int denominator) =>
        new Formula.Fraction(F.D((byte)numerator), F.D((byte)denominator));
    private static Formula Mul(Formula left, Formula right) =>
        F.Seq(left, F.Cdot, F.Sp, right);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
}
