using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Budget;

internal sealed class ExponentialFiniteMomentTransferDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exponentially bounded Cayley coefficients give a certified finite-moment tail.",
        H("Exponential Finite-Moment Transfer"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exponential-finite-moment-transfer"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/Budget/ExponentialFiniteMomentTransfer."
                        + "exponential_finite_moment_transfer"),
                H("Cayley moment truncation has an exponential tail bound"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The source and target moments are complex, while the scale, radius, "
                            + "and Cauchy envelope are real. The public statement retains the "
                            + "complete moment-transfer sum, the uniform moment bound, and the "
                            + "coefficient estimate at the chosen radius.")),
                    Paragraph(Text(
                        "The scale inequalities make the reciprocal radius a geometric ratio "
                            + "strictly between zero and one. Splitting the convergent transfer "
                            + "series after depth M and summing its norm majorant gives exactly "
                            + "the displayed remainder.")),
                    Paragraph(Text(
                        "Repository and pinned-library searches found no exact combined transfer "
                            + "theorem. The proof uses the library's natural-index tail split, "
                            + "norm-of-sum bound, and closed form for a real geometric series."))),
                DescribeRole.Theorem))));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula Power(Formula value, Formula exponent) =>
        Seq(value, Caret, Grp(exponent));

    private static Formula At(Formula sequence, Formula index) =>
        new Formula.Subscript(sequence, index);

    private static Formula TheoremFormula()
    {
        Formula natural = Naturals();
        Formula real = Reals();
        Formula complex = Complexes();
        Formula n = F.Id("n");
        Formula depth = F.Id("M");
        Formula r = F.Id("r");
        Formula rho = F.Id("rho");
        Formula radius = F.Id("R");
        Formula source = F.Id("m");
        Formula coefficient = F.Id("c");
        Formula target = F.Id("b");
        Formula k = F.Id("k");
        Formula absR = new Formula.Absolute(r);
        Formula inverseRho = Power(rho, Seq(Minus, D(1)));
        Formula envelope = new Formula.Fraction(
            Seq(
                Power(Seq(Open, D(1), Sp, Plus, Sp, absR, Close), D(2)), Sp,
                rho, Sp,
                Power(
                    Seq(Open, rho, Sp, Plus, Sp, absR, Close),
                    Seq(n, Sp, Minus, Sp, D(1)))),
            Power(
                Seq(Open, D(1), Sp, Minus, Sp, absR, Sp, rho, Close),
                Seq(n, Sp, Plus, Sp, D(1))));
        Formula sourceAtK = At(source, k);
        Formula coefficientAtK = At(coefficient, k);
        Formula summand = Seq(coefficientAtK, Sp, sourceAtK);
        Formula finiteSum = Seq(
            Sum, Underscore, Grp(Seq(k, Eq, D(0))), Caret, Grp(depth), Sp, summand);
        Formula coefficientLaw = Seq(
            Forall, Sp, k, Colon, Sp, natural, Comma, Sp,
            new Formula.Norm(coefficientAtK), Sp, Leq, Sp,
            envelope, Sp, Power(rho, Seq(Minus, k)));
        Formula momentLaw = Seq(
            Forall, Sp, k, Colon, Sp, natural, Comma, Sp,
            new Formula.Norm(sourceAtK), Sp, Leq, Sp, radius);
        Formula transferLaw = Call(
            "HasSum",
            Seq(k, Sp, Mapsto, Sp, summand),
            target);
        Formula tailBound = new Formula.Fraction(
            Seq(
                radius, Sp, envelope, Sp,
                Power(rho, Seq(Minus, Open, depth, Sp, Plus, Sp, D(1), Close))),
            Seq(D(1), Sp, Minus, Sp, inverseRho));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, n, Comma, Sp, depth, Colon, Sp, natural, Comma,
            RowBreak, Grp(),
            r, Comma, Sp, rho, Comma, Sp, radius, Colon, Sp, real, Comma,
            RowBreak, Grp(),
            source, Comma, Sp, coefficient, Colon, Sp, Arrow(natural, complex), Comma,
            target, Colon, Sp, complex, Comma,
            RowBreak, Grp(),
            Open, D(1), Sp, Lt, Sp, rho, Sp, Lt, Sp,
            Power(absR, Seq(Minus, D(1))), Close, Sp, Land,
            RowBreak, Grp(),
            Open, momentLaw, Close, Sp, Land,
            RowBreak, Grp(),
            Open, coefficientLaw, Close, Sp, Land,
            RowBreak, Grp(),
            transferLaw, Sp, Rightarrow,
            RowBreak, Grp(),
            new Formula.Norm(Seq(target, Sp, Minus, Sp, finiteSum)), Sp, Leq, Sp,
            tailBound, Dot,
            End, Grp(F.Id("gathered"))));
    }

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
