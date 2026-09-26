using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Asymptotics;

internal sealed class CosineIntegralLatticeDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Fourier/Asymptotics/CosineIntegralLattice.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The squared cosine-integral tail has a uniform bound on every positive lattice.",
        H("Cosine Integral on Positive Lattices"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("real-cosine-integral-tail"),
                DeclarationHandle.Create(Module + "cosineIntegral"),
                H("The real cosine-integral tail"),
                StatementSource.FromAuthor(DefinitionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For positive x, the integral of sin(t) / t^2 over (x,infinity) "
                        + "is absolutely convergent. The displayed representation has the "
                        + "usual convention Ci(x) equal to the negative improper integral "
                        + "of cos(t)/t from x to infinity. Integration by parts gives the "
                        + "sine boundary term with a positive sign and the remaining tail "
                        + "with a negative sign. The Lean definition is a total real function; "
                        + "the analytic interpretation here concerns positive arguments."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("uniform-cosine-integral-square-lattice-bound"),
                DeclarationHandle.Create(Module + "result"),
                H("One constant for all positive spacings"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "There is one positive real constant C, independent of the positive "
                        + "spacing z. The infinite series of squared Ci values at z,2z,3z,... "
                        + "is summable, and its sum multiplied by z is at most C.")),
                    Paragraph(Text(
                        "The elementary sine bounds imply absolute Ci bounds 5 times "
                        + "x to the power -1/4 and 2/x for every positive x. Squaring gives "
                        + "the nonnegative envelope E(x)=25 x^(-1/2) for 0<x<=1 and "
                        + "E(x)=25 x^(-2) for x>1. The two formulas agree at one. "
                        + "This envelope is decreasing and integrable on the positive half-line, "
                        + "and x E(x) is at most 25.")),
                    Paragraph(Text(
                        "Separate the first lattice point and compare the remaining terms "
                        + "with the integral from z to infinity. A change of variables cancels "
                        + "the factor z. The proof chooses C=26 plus the integral of E over "
                        + "the positive half-line. No lower bound on z and no finite truncation "
                        + "of the series is required. The statement is a deterministic analytic "
                        + "estimate and contains no stochastic convergence assertion."))),
                DescribeRole.Theorem))));

    private static Formula Reals => F.Seq(F.Mathbb, F.Grp(F.Id("R")));
    private static Formula Naturals => F.Seq(F.Mathbb, F.Grp(F.Id("N")));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [Bound(name, domain)], body);
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Times(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Square(Formula value) => new Formula.Power(value, F.D(2));

    private static Formula DefinitionFormula()
    {
        Formula x = F.Id("x");
        Formula t = F.Id("t");
        Formula tail = F.Seq(F.Int, F.Underscore, F.Grp(x), F.Caret, F.Grp(F.Infty),
            F.Sp, new Formula.Fraction(Call("sin", t), Square(t)),
            F.Sp, F.Id("d"), t);
        Formula rhs = new Formula.Binary(new Formula.Fraction(Call("sin", x), x),
            FormulaBinaryOperator.Subtract, tail);
        return F.Disp(ForAll("x", Reals,
            new Formula.Logic(Rel(F.D(0), FormulaRelationOperator.LessThan, x),
                FormulaLogicOperator.Implies,
                Rel(Call("Ci", x), FormulaRelationOperator.Equal, rhs))));
    }

    private static Formula TheoremFormula()
    {
        Formula c = F.Id("C");
        Formula z = F.Id("z");
        Formula n = F.Id("n");
        Formula sample = Square(Call("Ci", Times(z, F.Seq(F.Open, n, F.Plus, F.D(1), F.Close))));
        Formula series = F.Seq(F.Sum, F.Underscore,
            F.Grp(n, F.Sp, F.InMacro, F.Sp, Naturals), F.Sp, sample);
        Formula summable = Call("Summable", F.Seq(n, F.Colon, Naturals, F.Sp, F.Mapsto, F.Sp, sample));
        Formula bound = Rel(Times(z, series), FormulaRelationOperator.LessThanOrEqual, c);
        Formula positiveZ = Rel(F.D(0), FormulaRelationOperator.LessThan, z);
        Formula allZ = ForAll("z", Reals,
            new Formula.Logic(positiveZ, FormulaLogicOperator.Implies, And(summable, bound)));
        return F.Disp(new Formula.BindMany(FormulaQuantifier.Exists, [Bound("C", Reals)],
            And(Rel(F.D(0), FormulaRelationOperator.LessThan, c), allZ)));
    }
}
