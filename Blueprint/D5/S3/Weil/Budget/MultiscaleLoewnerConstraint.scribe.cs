using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Budget;

internal sealed class MultiscaleLoewnerConstraintDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One positive spectrum forces its multiscale budget matrix to be positive semidefinite.",
        H("Multiscale Loewner Constraint"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("multiscale-loewner-constraint"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/Budget/MultiscaleLoewnerConstraint."
                        + "multiscale_loewner_constraint"),
                H("A common resolvent spectrum gives a positive semidefinite scale matrix"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The measure is the common positive spectrum. Its budget curve and the "
                            + "piecewise divided-difference matrix are both constructed in the "
                            + "displayed proposition, including the derivative diagonal.")),
                    Paragraph(Text(
                        "Positive scales make every resolvent finite under the stated "
                            + "integrability law. Distinct scales are the domain condition for "
                            + "the off-diagonal quotient in the source formula.")),
                    Paragraph(Text(
                        "The proof identifies the matrix with the integral Gram kernel. A local "
                            + "half-scale resolvent dominates differentiation under the integral, "
                            + "so the diagonal identity is derived from the same measure."))),
                DescribeRole.Theorem))));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);

    private static Formula At(Formula value, Formula index) =>
        new Formula.Subscript(value, index);

    private static Formula TheoremFormula()
    {
        Formula natural = Naturals();
        Formula real = Reals();
        Formula count = F.Id("M");
        Formula measure = F.Id("nu");
        Formula scale = F.Id("u");
        Formula budget = F.Id("B");
        Formula loewner = F.Id("L");
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula t = F.Id("t");
        Formula xi = F.Id("xi");
        Formula finCount = Call("Fin", count);
        Formula scaleAtI = At(scale, i);
        Formula scaleAtJ = At(scale, j);
        Formula xiSquared = Power(xi, D(2));
        Formula resolventAtT = new Formula.Fraction(
            D(1), Seq(xiSquared, Sp, Plus, Sp, t));
        Formula budgetAtI = Apply(budget, scaleAtI);
        Formula budgetAtJ = Apply(budget, scaleAtJ);
        Formula dividedDifference = new Formula.Fraction(
            Seq(budgetAtI, Sp, Minus, Sp, budgetAtJ),
            Seq(scaleAtJ, Sp, Minus, Sp, scaleAtI));
        Formula diagonal = Seq(Minus, Call("deriv", budget, scaleAtI));
        Formula entryDefinition = Call(
            "if", Seq(i, Sp, Eq, Sp, j), diagonal, dividedDifference);
        Formula budgetDefinition = Seq(
            Operatorname, Grp(F.Id("let")), Sp,
            budget, Colon, Sp, Arrow(real, real), Sp, Colon, Eq, Sp,
            t, Sp, Mapsto, Sp, Call(
                "integral", measure, Seq(xi, Sp, Mapsto, Sp, resolventAtT)), Comma);
        Formula loewnerDefinition = Seq(
            Operatorname, Grp(F.Id("let")), Sp,
            loewner, Colon, Sp, Call("Matrix", finCount, finCount, real),
            Sp, Colon, Eq, Sp,
            Open, i, Comma, Sp, j, Close, Sp, Mapsto, Sp, entryDefinition, Comma);
        Formula positiveScales = Seq(
            Forall, Sp, i, Colon, Sp, finCount, Comma, Sp,
            D(0), Sp, Lt, Sp, scaleAtI);
        Formula finiteBudgets = Seq(
            Forall, Sp, t, Colon, Sp, real, Comma, Sp,
            D(0), Sp, Lt, Sp, t, Sp, Rightarrow, Sp,
            Call("Integrable", Seq(xi, Sp, Mapsto, Sp, resolventAtT), measure));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, count, Colon, Sp, natural, Comma,
            RowBreak, Grp(),
            measure, Colon, Sp, Call("Measure", real), Comma,
            RowBreak, Grp(),
            scale, Colon, Sp, Arrow(finCount, real), Comma,
            RowBreak, Grp(),
            Open, positiveScales, Close, Sp, Land,
            RowBreak, Grp(),
            Call("Injective", scale), Sp, Land,
            RowBreak, Grp(),
            Open, finiteBudgets, Close, Sp, Rightarrow,
            RowBreak, Grp(),
            budgetDefinition,
            RowBreak, Grp(),
            loewnerDefinition,
            RowBreak, Grp(),
            Call("PosSemidef", loewner), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Apply(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }
}
