using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.GermWindow;

internal sealed class GoldenGermThirdOrderWindowZeroCriterionDocument
    : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Analytic/GermWindow/GoldenGermThirdOrderWindowZeroCriterion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The frozen third-order golden residual vanishes exactly at a local-factor zero, "
            + "and RH classifies the continued germ's zeros in the open golden window.",
        H("Golden Germ Third-Order Window Zero Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-third-order-window-zero-on-line"),
                DeclarationHandle.Create(
                    Module + "golden_continued_germ_window_zero_on_line_of_rh"),
                H("RH puts every residual-surviving window zero on the pulled-back line"),
                StatementSource.FromAuthor(WindowZeroOnLineFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The displayed Kp is the frozen normalized third-order local "
                            + "factor and G3 is its prime product. Under RH, a zero of the "
                            + "continued germ in the open window has real part one over "
                            + "twice phi squared whenever G3 survives there.")),
                    Paragraph(Text(
                        "The agreement and five-zeta factorization premises are the two "
                            + "clauses of the frozen third-order continuation theorem. This "
                            + "is a conditional zero-confinement result, not a proof of RH."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-third-residual-local-factor-zero"),
                DeclarationHandle.Create(
                    Module + "golden_third_residual_eq_zero_iff_exists_local_factor_zero"),
                H("Third-order residual zeros are exactly local-factor zeros"),
                StatementSource.FromAuthor(ResidualZeroFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Above the phi-fifth boundary, the norm-summable deviation of Kp "
                            + "from one makes the infinite product nonzero whenever every "
                            + "canonical local factor is nonzero. Conversely, one zero "
                            + "factor forces the product G3 to vanish.")),
                    Paragraph(Text(
                        "Thus G3's zero set in this half-plane is exactly the union of the "
                            + "local-factor zero sets. The equivalence does not itself "
                            + "assert the existence of such a zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-continued-germ-window-zero-iff-rh"),
                DeclarationHandle.Create(
                    Module + "golden_continued_germ_window_zero_iff_of_rh"),
                H("RH identifies the continued germ's complete open-window zero set"),
                StatementSource.FromAuthor(WindowZeroIffFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Under RH, a continued germ satisfying the frozen third-order "
                            + "formula vanishes in the open window exactly when either the "
                            + "phi-squared zeta pullback vanishes on its pulled-back "
                            + "critical line or some canonical local factor vanishes.")),
                    Paragraph(Text(
                        "This classification is not an RH proof path. The numerical "
                            + "local-factor zeros for p = 2 and p = 3 make the naive claim "
                            + "that window zeros lie on the line if and only if RH false."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/EulerGerm/GoldenGermThirdOrderFactorization")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/EulerGerm/GoldenGermWindowZeroCriterion")),
        ]));

    private static Formula WindowZeroOnLineFormula()
    {
        Formula continuedGerm = F.Id("continuedGerm");
        Formula s = F.Id("s");
        Formula domain = ContinuationDomain(s);
        Formula agreement = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", domain)],
            Implies(
                Less(PhiThreshold(2), RealPart(s)),
                Equal(
                    Apply(continuedGerm, s),
                    PrimeProduct(LocalFactor(s, F.Id("p"))))));
        Formula factorization = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", domain)],
            Equal(Apply(continuedGerm, s), ContinuedFormula(s)));
        Formula conclusion = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", domain)],
            Implies(
                LowerWindow(s),
                Implies(
                    UpperWindow(s),
                    Implies(
                        Equal(Apply(continuedGerm, s), F.D(0)),
                        Implies(
                            NotEqual(G3(s), F.D(0)),
                            Equal(RealPart(s), CriticalLine()))))));
        Formula theorem = Implies(
            F.Id("RiemannHypothesis"),
            new Formula.BindMany(
                FormulaQuantifier.ForAll,
                [Bound("continuedGerm", new Formula.TypeArrow(domain, ComplexNumbers()))],
                Implies(And(agreement, factorization), conclusion)));

        return WithResidualDefinitions(theorem);
    }

    private static Formula ResidualZeroFormula()
    {
        Formula s = F.Id("s");
        Formula p = F.Id("p");
        Formula localZero = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("p", Primes())],
            Equal(LocalFactor(s, p), F.D(0)));
        Formula zeroIff = Iff(Equal(G3(s), F.D(0)), localZero);
        Formula theorem = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", ComplexNumbers())],
            Implies(Less(PhiThreshold(5), RealPart(s)), zeroIff));

        return WithResidualDefinitions(theorem);
    }

    private static Formula WindowZeroIffFormula()
    {
        Formula continuedGerm = F.Id("continuedGerm");
        Formula s = F.Id("s");
        Formula p = F.Id("p");
        Formula domain = ContinuationDomain(s);
        Formula primaryZero = And(
            Equal(Zeta(Multiply(PhiPower(2), s)), F.D(0)),
            Equal(RealPart(s), CriticalLine()));
        Formula localZero = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("p", Primes())],
            Equal(LocalFactor(s, p), F.D(0)));
        Formula zeroClassification = Iff(
            Equal(Apply(continuedGerm, s), F.D(0)),
            Or(primaryZero, localZero));
        Formula conclusion = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", domain)],
            Implies(LowerWindow(s), Implies(UpperWindow(s), zeroClassification)));
        Formula factorization = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", domain)],
            Equal(Apply(continuedGerm, s), ContinuedFormula(s)));
        Formula theorem = Implies(
            F.Id("RiemannHypothesis"),
            new Formula.BindMany(
                FormulaQuantifier.ForAll,
                [Bound("continuedGerm", new Formula.TypeArrow(domain, ComplexNumbers()))],
                Implies(factorization, conclusion)));

        return WithResidualDefinitions(theorem);
    }

    private static Formula WithResidualDefinitions(Formula theorem)
    {
        Formula s = F.Id("s");
        Formula p = F.Id("p");
        Formula x = Call("x", s, p);
        Formula y = Call("y", s, p);
        Formula kp = Kp(s, p);
        Formula xDefinition = F.Seq(
            x, F.Sp, F.Colon, F.Eq, F.Sp,
            Power(p, F.Seq(F.Minus, s, F.Sp, F.Times, F.Sp, PhiPower(2))));
        Formula yDefinition = F.Seq(
            y, F.Sp, F.Colon, F.Eq, F.Sp,
            Power(p, F.Seq(F.Minus, s, F.Sp, F.Times, F.Sp, PhiPower(3))));
        Formula kpDefinition = F.Seq(
            kp, F.Sp, F.Colon, F.Eq, F.Sp,
            NormalizedFactor(LocalFactor(s, p), x, y));
        Formula gDefinition = F.Seq(
            F.Forall, F.Sp, s, F.InMacro, F.Sp, ComplexNumbers(), F.Comma, F.Sp,
            G3(s), F.Sp, F.Colon, F.Eq, F.Sp, PrimeProduct(kp));

        return F.Disp(new Formula.Aligned([
            F.Seq(
                F.Forall, F.Sp, s, F.InMacro, F.Sp, ComplexNumbers(), F.Comma,
                F.Sp, p, F.InMacro, F.Sp, Primes(), F.Comma),
            F.Seq(
                xDefinition, F.Comma, F.Sp, yDefinition, F.Comma, F.Sp,
                kpDefinition, F.Comma),
            F.Seq(gDefinition, F.Comma),
            F.Seq(theorem, F.Dot),
        ]));
    }

    private static Formula ContinuedFormula(Formula s)
    {
        Formula zetaSquared = Zeta(Multiply(PhiPower(2), s));
        Formula zetaCubed = Zeta(Multiply(PhiPower(3), s));
        Formula zetaDoubleSquared = Zeta(
            Multiply(Multiply(F.D(2), PhiPower(2)), s));
        Formula zetaDoubleCubed = Zeta(
            Multiply(Multiply(F.D(2), PhiPower(3)), s));
        Formula zetaMixed = Zeta(
            Multiply(Add(Multiply(F.D(2), PhiPower(2)), PhiPower(3)), s));

        return Multiply(
            Multiply(
                Multiply(zetaSquared, zetaCubed),
                Inverse(zetaDoubleSquared)),
            Multiply(Multiply(Inverse(zetaDoubleCubed), zetaMixed), G3(s)));
    }

    private static Formula NormalizedFactor(Formula local, Formula x, Formula y)
    {
        Formula oneMinusYSquared = F.Seq(
            F.Open, F.D(1), F.Sp, F.Minus, F.Sp, Power(y, F.D(2)), F.Close);
        Formula oneMinusXSquaredY = F.Seq(
            F.Open, F.D(1), F.Sp, F.Minus, F.Sp,
            Power(x, F.D(2)), F.Sp, F.Times, F.Sp, y, F.Close);
        Formula oneMinusY = F.Seq(
            F.Open, F.D(1), F.Sp, F.Minus, F.Sp, y, F.Close);
        Formula onePlusX = F.Seq(
            F.Open, F.D(1), F.Sp, F.Plus, F.Sp, x, F.Close);

        return F.Seq(
            Inverse(oneMinusYSquared),
            F.Sp, F.Times, F.Sp, oneMinusXSquaredY,
            F.Sp, F.Times, F.Sp, oneMinusY,
            F.Sp, F.Times, F.Sp, Inverse(onePlusX),
            F.Sp, F.Times, F.Sp, local);
    }

    private static Formula ContinuationDomain(Formula s) =>
        new Formula.SetBuilder(
            Less(PhiThreshold(5), RealPart(s)), s, ComplexNumbers());

    private static Formula LowerWindow(Formula s) =>
        Less(Fraction(F.D(1), Multiply(F.D(2), PhiPower(3))), RealPart(s));

    private static Formula UpperWindow(Formula s) =>
        Less(RealPart(s), PhiThreshold(2));

    private static Formula CriticalLine() =>
        Fraction(F.D(1), Multiply(F.D(2), PhiPower(2)));

    private static Formula PhiThreshold(byte exponent) =>
        Fraction(F.D(1), PhiPower(exponent));

    private static Formula PhiPower(byte exponent) =>
        new Formula.Power(F.Varphi, F.D(exponent));

    private static Formula Kp(Formula s, Formula p) => Call("Kp", s, p);

    private static Formula G3(Formula s) => Call("G3", s);

    private static Formula LocalFactor(Formula s, Formula p) =>
        Call("germLocalFactor", s, p);

    private static Formula PrimeProduct(Formula body) =>
        F.Seq(F.Prod, F.Underscore, F.Grp(
            F.Id("p"), F.InMacro, F.Sp, Primes()), body);

    private static Formula Primes() => Call("Primes", NaturalNumbers());

    private static Formula Zeta(Formula value) => Call("riemannZeta", value);

    private static Formula RealPart(Formula value) => F.Seq(F.Re, F.Grp(value));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);

    private static Formula Power(Formula value, Formula exponent) =>
        F.Seq(value, F.Caret, F.Grp(exponent));

    private static Formula Inverse(Formula value) =>
        new Formula.Power(value, F.Seq(F.Minus, F.D(1)));

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Or, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula ComplexNumbers() =>
        F.Seq(F.Mathbb, F.Grp(F.Id("C")));

    private static Formula NaturalNumbers() =>
        F.Seq(F.Mathbb, F.Grp(F.Id("N")));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
