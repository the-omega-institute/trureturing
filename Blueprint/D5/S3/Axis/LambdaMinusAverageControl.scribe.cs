using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Axis;

internal sealed class LambdaMinusAverageControlDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The diagonal prime-axis sum controls the contraction-face average with the exact golden scale.",
        H("Diagonal Control of the Contraction-Face Average"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("lambda-minus-average-diagonal-control"),
                DeclarationHandle.Create(
                    "D5/S3/Axis/LambdaMinusAverageControl."
                        + "lambda_minus_average_diagonal_control"),
                H("The diagonal prime-axis average transfers to the contraction face"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The diagonal summatory function is assembled prime-first. For each prime "
                            + "below the cutoff, it sums the contraction reading of that prime's "
                            + "factorization exponent over the integers below the cutoff.")),
                    Paragraph(Text(
                        "Finite-sum interchange proves that this independently assembled diagonal "
                            + "quantity is exactly the summatory lambdaMinus function. Consequently, "
                            + "the displayed diagonal asymptotic premise transfers without loss to "
                            + "the contraction-face average.")),
                    Paragraph(Text(
                        "The existing Dirichlet-series theorem supplies the zeta factor. The first "
                            + "contraction exponent is evaluated exactly as the square of the golden "
                            + "conjugate; the decimal approximation and finite-window measurement are "
                            + "empirical remarks and are not theorem conjuncts.")),
                    Paragraph(Text(
                        "The reverse analytic-information direction remains an open semantic status "
                            + "remark in the source and is not encoded as a claim of formal "
                            + "unprovability."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula s = F.Id("s");
        Formula x = F.Id("x");
        Formula n = F.Id("n");
        Formula p = F.Id("p");
        Formula atTop = F.Id("atTop");
        Formula psiSquared = Seq(Psi, Caret, Grp(D(2)));
        Formula axisSum = Apply(F.Id("lambdaMinusPrimeAxisSummatory"), x);
        Formula denominator = Seq(
            Open, x, Colon, real, Close, Sp, Cdot, Sp, Call("log", x));
        Formula summatory = Seq(
            Sum, Underscore, Grp(D(0), Sp, Leq, Sp, n, Sp, Leq, Sp, x), Sp,
            Apply(F.Id("lambdaMinus"), n));
        Formula axisLimit = Call(
            "Tendsto",
            Seq(Open, Typed(x, natural), Close, Sp, Mapsto, Sp,
                Frac, Grp(axisSum), Grp(denominator)),
            atTop,
            Call("nhds", psiSquared));
        Formula summatoryLimit = Call(
            "Tendsto",
            Seq(Open, Typed(x, natural), Close, Sp, Mapsto, Sp,
                Frac, Grp(summatory), Grp(denominator)),
            atTop,
            Call("nhds", psiSquared));
        Formula supportCondition = Seq(
            p, Sp, InMacro, Sp, Call("support", Call("factorization", n)));
        Formula axisTerm = Call(
            "if",
            supportCondition,
            Seq(
                Apply(F.Id("betaContraction"), Apply(Call("factorization", n), p)),
                Sp, Cdot, Sp, Call("log", p)),
            D(0));
        Formula axisDefinition = Seq(
            Forall, Sp, Typed(x, natural), Comma, Sp,
            axisSum, Sp, Colon, Eq, Sp,
            Sum, Underscore,
            Grp(p, Sp, Lt, Sp, x, Plus, D(1), Comma, Sp,
                p, Sp, F.Text, Grp(F.Id("prime"))), Sp,
            Sum, Underscore,
            Grp(D(0), Sp, Leq, Sp, n, Sp, Leq, Sp, x), Sp,
            axisTerm, Semi);
        Formula dirichletFactor = Seq(
            Call("LSeries", F.Id("lambdaMinus"), s), Sp, Eq, Sp,
            Zeta, Open, s, Close, Sp, Cdot, Sp,
            Apply(F.Id("lambdaMinusAxisSeries"), s));
        Formula finiteBridge = Seq(
            Forall, Sp, Typed(x, natural), Comma, Sp,
            summatory, Sp, Eq, Sp, axisSum);
        Formula betaOne = Seq(
            Apply(F.Id("betaContraction"), D(1)), Sp, Eq, Sp, psiSquared);

        return Disp(new Formula.Aligned([
            axisDefinition,
            Seq(Forall, Sp, Typed(s, complex), Comma, Sp,
                D(1), Sp, Lt, Sp, Re, Open, s, Close, Comma),
            Seq(Grp(), dirichletFactor, Sp, Land),
            Seq(Grp(), Open, finiteBridge, Close, Sp, Land),
            Seq(Grp(), Open, axisLimit, Sp, Rightarrow, Sp,
                summatoryLimit, Close, Sp, Land),
            Seq(Grp(), betaOne, Dot),
        ]));
    }

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var pieces = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) pieces.AddRange([Comma, Sp]);
            pieces.Add(arguments[index]);
        }

        pieces.Add(Close);
        return Seq([.. pieces]);
    }
}
