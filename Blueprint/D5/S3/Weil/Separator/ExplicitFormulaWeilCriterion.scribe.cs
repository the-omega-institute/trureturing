using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Separator;

internal sealed class ExplicitFormulaWeilCriterionDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/Separator/ExplicitFormulaWeilCriterion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Relative to supplied zero data and an explicit archimedean-integrability "
            + "hypothesis, RH is equivalent to nonnegativity of the classical "
            + "pole-minus-prime-plus-archimedean expression on every convolution square.",
        H("Explicit-Formula Weil Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("explicit-formula-weil-square"),
                DeclarationHandle.Create(Prefix + "explicitFormula_weilSquare"),
                H("The explicit formula for a convolution square"),
                StatementSource.FromAuthor(ExplicitFormulaStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The frozen zeta explicit formula is applied to convolutionSquare(g). "
                            + "The supplied ZeroData gives its canonical symmetric-convergence "
                            + "witness, while hArch is exactly the assumed integrability of the "
                            + "displayed digamma integral; that integrability is not proved here.")),
                    Paragraph(Text(
                        "The display expands the pole evaluations, the von Mangoldt series "
                            + "Lambda(n)/sqrt(n) times the two logarithmic samples, and the "
                            + "archimedean digamma integral term by term."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rh-iff-explicit-formula-positivity"),
                DeclarationHandle.Create(Prefix + "rh_iff_explicitFormulaPositivity"),
                H("RH is equivalent to explicit-formula positivity"),
                StatementSource.FromAuthor(CriterionStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The frozen Weil-square positivity criterion and the preceding explicit "
                            + "formula rewrite each side of the equivalence. Proof irrelevance "
                            + "identifies an arbitrary symmetric-convergence witness with the "
                            + "canonical witness supplied by ZeroData.")),
                    Paragraph(Text(
                        "The universal hArch premise is explicit: archimedean integrability of "
                            + "every convolution square is assumed, not established in this "
                            + "module. The theorem is relative to a supplied ZeroData; existence "
                            + "of such data is not asserted, and M1-b remains open.")),
                    Paragraph(Text(
                        "WeilTestFunction here means this repository's even, smooth, compactly "
                            + "supported test functions, not the wider classes used in parts of "
                            + "the literature. This conditional equivalence is not a proof of the "
                            + "Riemann hypothesis."))),
                DescribeRole.Theorem)),
        []));

    private static Formula ExplicitFormulaStatement()
    {
        Formula zeroData = F.Id("Z");
        Formula test = F.Id("g");
        Formula hArch = F.Id("hArch");
        Formula square = Square(test);
        Formula zeroSide = Call(
            "zeroSum",
            zeroData,
            square,
            Call("symmetricConvergentOfZeroData", zeroData, square));
        Formula statement = ForAll(
            [
                Bound("Z", F.Id("ZeroData")),
                Bound("g", F.Id("WeilTestFunction")),
                Bound("hArch", Call("ArchimedeanConvergent", square)),
            ],
            Equal(zeroSide, PrimeSide(square, hArch)));

        return WithExpansions(statement, test, hArch);
    }

    private static Formula CriterionStatement()
    {
        Formula zeroData = F.Id("Z");
        Formula test = F.Id("g");
        Formula hArch = F.Id("hArch");
        Formula square = Square(test);
        Formula hArchAtTest = Apply(hArch, test);
        Formula hArchType = ForAll(
            [Bound("g", F.Id("WeilTestFunction"))],
            Call("ArchimedeanConvergent", Square(F.Id("g"))));
        Formula positivity = ForAll(
            [Bound("g", F.Id("WeilTestFunction"))],
            LessOrEqual(D(0), RealPart(PrimeSide(square, hArchAtTest))));
        Formula statement = ForAll(
            [Bound("Z", F.Id("ZeroData")), Bound("hArch", hArchType)],
            Iff(RiemannHypothesis(), positivity));

        return WithExpansions(statement, test, hArchAtTest);
    }

    private static Formula WithExpansions(
        Formula statement, Formula test, Formula archWitness)
    {
        Formula square = Square(test);

        return Disp(new Formula.Aligned([
            statement,
            Seq(F.Text, Grp(F.Id("where")), Sp),
            Seq(Equal(Call("poleTerm", square), PoleExpansion(square))),
            Seq(Equal(Call("primeTerm", square), PrimeExpansion(test))),
            Seq(Equal(
                Call("archimedeanTerm", square, archWitness),
                ArchimedeanExpansion(square))),
        ]));
    }

    private static Formula PrimeSide(Formula square, Formula archWitness) =>
        Add(
            Subtract(Call("poleTerm", square), Call("primeTerm", square)),
            Call("archimedeanTerm", square, archWitness));

    private static Formula PoleExpansion(Formula square)
    {
        Formula halfI = new Formula.Fraction(F.Id("i"), D(2));
        return Add(
            Call("fourierLaplace", square, Seq(Minus, halfI)),
            Call("fourierLaplace", square, halfI));
    }

    private static Formula PrimeExpansion(Formula test)
    {
        Formula n = F.Id("n");
        Formula logN = Seq(Log, Open, n, Close);
        Formula squareAtPositiveLog = Apply(Square(test), logN);
        Formula squareAtNegativeLog =
            Apply(Square(test), Seq(Minus, logN));
        Formula mangoldtWeight = new Formula.Fraction(
            Seq(Lambda, Open, n, Close),
            Seq(Sqrt, Grp(n)));
        Formula samples = Add(squareAtPositiveLog, squareAtNegativeLog);

        return Seq(
            Sum, Underscore, Grp(n, Sp, InMacro, Sp, Naturals()), Sp,
            Multiply(mangoldtWeight, samples));
    }

    private static Formula ArchimedeanExpansion(Formula square)
    {
        Formula t = F.Id("t");
        Formula quarter = new Formula.Fraction(D(1), D(4));
        Formula imaginaryPart = new Formula.Fraction(
            Multiply(F.Id("i"), t), D(2));
        Formula digammaArgument = Add(quarter, imaginaryPart);
        Formula density = Subtract(
            RealPart(Seq(Psi, Open, digammaArgument, Close)),
            Call("log", Pi));
        Formula integrand = Multiply(
            density, Call("fourierLaplace", square, t));
        Formula integral = Seq(
            Int, Underscore, Grp(Reals()), Sp,
            integrand, Sp, F.Id("d"), t);

        return Multiply(
            new Formula.Fraction(D(1), Seq(D(2), Pi)),
            integral);
    }

    private static Formula Square(Formula test) =>
        Call("convolutionSquare", test);

    private static Formula RiemannHypothesis() =>
        Seq(Operatorname, Grp(F.Id("RiemannHypothesis")));

    private static Formula RealPart(Formula value) =>
        Seq(Re, Sp, Open, value, Close);

    private static Formula Naturals() =>
        Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Reals() =>
        Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula ForAll(
        Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(
            left, FormulaRelationOperator.LessThanOrEqual, right);
}
