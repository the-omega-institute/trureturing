using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.TestFunctions;

internal sealed class FiniteMomentEliminationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula real = Call("Real"), complex = Call("Complex"), natural = Call("Natural");
        Formula L = F.Id("L"), K = F.Id("K"), epsilon = F.Id("epsilon");
        Formula f = F.Id("f"), h = F.Id("h"), b = F.Id("b"), j = F.Id("j");
        Formula u = F.Id("u"), test = F.Id("test"), p = F.Id("p");
        Formula hfSmooth = F.Id("hfSmooth"), hhSmooth = F.Id("hhSmooth");
        Formula hfCompact = F.Id("hfCompact"), hhCompact = F.Id("hhCompact");
        Formula moment = F.Id("moment"), measureDistribution = F.Id("measureDistribution");
        Formula correction = F.Id("correction");
        Formula correctedDistribution = F.Id("correctedDistribution");
        Formula correlation = F.Id("correlation");
        Formula correlationCompact = F.Id("hcorrelationCompact");
        Formula correlationSmooth = F.Id("hcorrelationSmooth");
        Formula correlationTest = F.Id("correlationTest");

        Formula functionType = new Formula.TypeArrow(real, complex);
        Formula signedMeasure = Call("SignedMeasure", real);
        Formula distributionType = Call("TemperedDistribution", real, complex);
        Formula schwartzType = Call("SchwartzMap", real, complex);
        Formula polynomialType = Call("Polynomial", real);
        Formula doubledScale = Mul(D(2), L);
        Formula sourceInterval = Call("Icc", D(0), doubledScale);
        Formula innerInterval = Call("Ioo", new Formula.Negate(L), L);
        Formula jordan = Call("toJordanDecomposition", epsilon);
        Formula positivePart = Call("posPart", jordan);
        Formula negativePart = Call("negPart", jordan);
        Formula hpos = Equal(Call("restrict", positivePart, sourceInterval), positivePart);
        Formula hneg = Equal(Call("restrict", negativePart, sourceInterval), negativePart);

        Formula momentAt = SignedIntegral(
            epsilon,
            u,
            Pow(Sub(u, b), j));
        Formula measureDistributionDefinition = Sub(
            Call("toTemperedDistribution", positivePart),
            Call("toTemperedDistribution", negativePart));
        Formula coefficient = Call(
            "complex",
            Div(
                Mul(Pow(new Formula.Negate(D(1)), Add(j, D(1))), Apply(moment, j)),
                Call("factorial", j)));
        Formula deltaJet = Call(
            "iterate",
            Call("temperedDerivative", complex),
            j,
            Call("delta", b));
        Formula correctionDefinition = Call(
            "sum",
            j,
            Call("range", Add(K, D(1))),
            Call("smul", coefficient, deltaJet));
        Formula correlationDefinition = Call("weilTest", f, h);
        Formula compactDefinition = Call(
            "weilTestHasCompactSupport", hfCompact, hhCompact);
        Formula smoothDefinition = Call(
            "weilTestContDiff", hfSmooth, hhSmooth, hhCompact);
        Formula testDefinition = Call(
            "toSchwartzMap", correlation, correlationCompact, correlationSmooth);

        Formula schwartzJet = Call(
            "iterate",
            Call("schwartzDerivative", complex, complex),
            j,
            test);
        Formula distributionAction = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("test", schwartzType)],
            Equal(
                Apply(correctedDistribution, test),
                Add(
                    SignedIntegral(epsilon, u, Apply(test, u)),
                    Call(
                        "sum",
                        j,
                        Call("range", Add(K, D(1))),
                        Mul(
                            coefficient,
                            Mul(
                                Pow(Call("complex", new Formula.Negate(D(1))), j),
                                Apply(schwartzJet, b)))))));

        Formula realCoefficient = Div(
            Mul(Pow(new Formula.Negate(D(1)), Add(j, D(1))), Apply(moment, j)),
            Call("factorial", j));
        Formula polynomialJet = Call(
            "iterate",
            Call("polynomialDerivative", real),
            j,
            p);
        Formula polynomialAction = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("p", polynomialType)],
            Implies(
                LessOrEqual(Call("natDegree", p), K),
                Equal(
                    Add(
                        SignedIntegral(epsilon, u, Call("eval", p, u)),
                        Call(
                            "sum",
                            j,
                            Call("range", Add(K, D(1))),
                            Mul(
                                realCoefficient,
                                Mul(
                                    Pow(new Formula.Negate(D(1)), j),
                                    Call("eval", polynomialJet, b))))),
                    D(0))));
        Formula unchangedCorrelation = Equal(
            Apply(correctedDistribution, correlationTest),
            Apply(measureDistribution, correlationTest));

        Formula statement = Disp(new Formula.Aligned([
            Seq(Forall, Sp, L, Colon, Sp, real, Comma, Sp,
                K, Colon, Sp, natural, Comma, Sp,
                epsilon, Colon, Sp, signedMeasure, Comma),
            Seq(F.Id("hpos"), Colon, Sp, hpos, Comma, Sp,
                F.Id("hneg"), Colon, Sp, hneg, Comma),
            Seq(f, Comma, Sp, h, Colon, Sp, functionType, Comma, Sp,
                hfSmooth, Colon, Sp, Call("ContDiff", real, Call("infinity"), f), Comma),
            Seq(hhSmooth, Colon, Sp, Call("ContDiff", real, Call("infinity"), h), Comma, Sp,
                hfCompact, Colon, Sp, Call("HasCompactSupport", f), Comma),
            Seq(hhCompact, Colon, Sp, Call("HasCompactSupport", h), Comma, Sp,
                F.Id("hfSupport"), Colon, Sp, Call("tsupport", f), Sp, Subseteq, Sp,
                innerInterval, Comma),
            Seq(F.Id("hhSupport"), Colon, Sp, Call("tsupport", h), Sp, Subseteq, Sp,
                innerInterval, Sp, Rightarrow),
            LetDefinition(b, doubledScale),
            LetDefinition(moment, Call("lambda", j, momentAt)),
            LetTypedDefinition(
                measureDistribution,
                distributionType,
                measureDistributionDefinition),
            LetTypedDefinition(correction, distributionType, correctionDefinition),
            LetDefinition(
                correctedDistribution,
                Add(measureDistribution, correction)),
            LetDefinition(correlation, correlationDefinition),
            LetTypedDefinition(
                correlationCompact,
                Call("HasCompactSupport", correlation),
                compactDefinition),
            LetTypedDefinition(
                correlationSmooth,
                Call("ContDiff", real, Call("infinity"), correlation),
                smoothDefinition),
            LetDefinition(correlationTest, testDefinition),
            Seq(distributionAction, Sp, Land, Sp, polynomialAction, Sp, Land, Sp,
                unchangedCorrelation, Dot),
        ]));

        return DocumentDefinition.Create(ScribeNode.Create(
            "An endpoint delta jet cancels finitely many centered moments without changing "
                + "the Weil correlation pairing.",
            H("Finite-Moment Elimination"),
            Blocks(Describe.Lean(
                DescribeId.Create("finite-moment-elimination"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/TestFunctions/FiniteMomentElimination."
                        + "finite_moment_elimination"),
                H("Finite moment elimination by an endpoint delta jet"),
                StatementSource.FromAuthor(statement),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The signed measure is embedded canonically through its Jordan parts. "
                        + "A finite Taylor expansion proves polynomial annihilation, while "
                        + "strict doubled-window support makes every endpoint jet vanish on "
                        + "the constructed Weil correlation."))),
                DescribeRole.Theorem))));
    }

    private static Formula LetDefinition(Formula name, Formula value) =>
        Seq(Operatorname, Grp(F.Id("let")), Sp, name, Sp, Colon, Eq, Sp, value, Comma);

    private static Formula LetTypedDefinition(Formula name, Formula type, Formula value) =>
        Seq(Operatorname, Grp(F.Id("let")), Sp, name, Colon, Sp, type,
            Sp, Colon, Eq, Sp, value, Comma);

    private static Formula SignedIntegral(Formula measure, Formula variable, Formula body) =>
        Call("signedIntegral", variable, body, measure);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Pow(Formula value, Formula exponent) =>
        Call("pow", value, exponent);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Div(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
}
