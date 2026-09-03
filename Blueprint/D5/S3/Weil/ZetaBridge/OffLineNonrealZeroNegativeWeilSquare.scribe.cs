using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class OffLineNonrealZeroNegativeWeilSquareDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/ZetaBridge/OffLineNonrealZeroNegativeWeilSquare.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An off-line nonreal zero admits a powered even separator whose full Weil-square "
            + "zero sum has strictly negative real part.",
        H("Off-Line Nonreal Zero Negative Weil Square"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("off-line-nonreal-zero-negative-weil-square"),
                DeclarationHandle.Create(
                    Prefix + "offLineNonrealZero_yields_negative_weil_square"),
                H("An off-line nonreal zero yields a negative full Weil-square zero sum"),
                StatementSource.FromAuthor(NegativeSquareFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Finite even interpolation first prescribes a unit peak and an "
                            + "exception killer. Convolution powering preserves the target "
                            + "values while the frozen closed-strip decay makes the complement "
                            + "geometrically small.")),
                    Paragraph(Text(
                        "Frozen zeta-zero absolute summability identifies every symmetric "
                            + "zero-sum witness with the ordinary sum. Splitting that sum into "
                            + "the four-point orbit and its complement leaves the prescribed "
                            + "negative orbit larger in magnitude than the tail.")),
                    Paragraph(Text(
                        "The explicit nonzero imaginary-part hypothesis is the M3-d input. "
                            + "The theorem is conditional on that input and asserts no "
                            + "implication from O-6 to the Riemann hypothesis."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("peak-and-finite-exception-killer"),
                DeclarationHandle.Create(
                    Prefix + "exists_peak_and_finite_exception_killer"),
                H("A unit peak and finite-exception killer exist"),
                StatementSource.FromAuthor(PeakKillerFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The exceptional set is a sufficiently large symmetric spectral ball. "
                        + "Closed-strip decay bounds the peak function outside it, while finite "
                        + "even interpolation makes the killer vanish at every exceptional "
                        + "frequency away from the target orbit and prescribes opposite values "
                        + "on the target conjugate pair."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("burnol-power-tail-bound"),
                DeclarationHandle.Create(Prefix + "burnol_power_tail_bound"),
                H("The powered complement obeys Burnol's geometric tail bound"),
                StatementSource.FromAuthor(BurnolTailFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Outside the target orbit, exceptional indices vanish by the killer and "
                        + "all remaining indices acquire a factor at most one quarter at each "
                        + "convolution-power step. Absolute zeta-zero summability supplies the "
                        + "full majorant and permits summation over the subtype complement."))),
                DescribeRole.Theorem)),
        []));

    private static Formula NegativeSquareFormula()
    {
        Formula zeroData = F.Id("Z");
        Formula index = F.Id("n");
        Formula test = F.Id("g");
        Formula witness = F.Id("hZero");
        Formula square = Square(test);
        Formula premises = OffLineNonrealPremises(zeroData, index);
        Formula zeroSum = Call("zeroSum", zeroData, square, witness);
        Formula conclusion = Exists(
            [
                Bound("g", F.Id("WeilTestFunction")),
                Bound("hZero", Call("SymmetricConvergent", zeroData, square)),
            ],
            LessThan(RealPart(zeroSum), D(0)));

        return Disp(ForAll(
            [Bound("Z", F.Id("ZeroData")), Bound("n", Naturals())],
            Implies(premises, conclusion)));
    }

    private static Formula PeakKillerFormula()
    {
        Formula zeroData = F.Id("Z");
        Formula index = F.Id("n");
        Formula b = F.Id("b");
        Formula k = F.Id("k");
        Formula exceptional = F.Id("E");
        Formula j = F.Id("j");
        Formula gamma = Gamma(zeroData, index);
        Formula gammaJ = Gamma(zeroData, j);
        Formula conjugateGamma = Call("conj", gamma);
        Formula conjugateGammaJ = Call("conj", gammaJ);
        Formula orbit = Call("zeroOrbit", zeroData, index);
        Formula jInExceptional = Member(j, exceptional);
        Formula jOutsideExceptional = NotMember(j, exceptional);
        Formula jOutsideOrbit = NotMember(j, orbit);

        Formula reflectionClosed = ForAll(
            [Bound("j", Naturals())],
            Iff(Member(j, exceptional),
                Member(Call("reflection", zeroData, j), exceptional)));
        Formula conjugationClosed = ForAll(
            [Bound("j", Naturals())],
            Iff(Member(j, exceptional),
                Member(Call("conjugation", zeroData, j), exceptional)));
        Formula orbitIncluded = Seq(orbit, Sp, Subseteq, Sp, exceptional);
        Formula peakTail = ForAll(
            [Bound("j", Naturals())],
            Implies(
                jOutsideExceptional,
                And(
                    LessOrEqual(Norm(Transform(b, gammaJ)), Half()),
                    LessOrEqual(Norm(Transform(b, conjugateGammaJ)), Half()))));
        Formula killerZeros = ForAll(
            [Bound("j", Naturals())],
            Implies(
                And(jInExceptional, jOutsideOrbit),
                And(
                    Equal(Transform(k, gammaJ), D(0)),
                    Equal(Transform(k, conjugateGammaJ), D(0)))));
        Formula properties = And(
            reflectionClosed,
            conjugationClosed,
            orbitIncluded,
            Equal(Transform(b, gamma), D(1)),
            Equal(Transform(b, conjugateGamma), D(1)),
            Equal(Transform(k, gamma), D(1)),
            Equal(Transform(k, conjugateGamma), NegativeOne()),
            peakTail,
            killerZeros);
        Formula conclusion = Exists(
            [
                Bound("b", F.Id("WeilTestFunction")),
                Bound("k", F.Id("WeilTestFunction")),
                Bound("E", Call("Finset", Naturals())),
            ],
            properties);

        return Disp(ForAll(
            [Bound("Z", F.Id("ZeroData")), Bound("n", Naturals())],
            Implies(OffLineNonrealPremises(zeroData, index), conclusion)));
    }

    private static Formula BurnolTailFormula()
    {
        Formula zeroData = F.Id("Z");
        Formula target = F.Id("n");
        Formula b = F.Id("b");
        Formula k = F.Id("k");
        Formula exceptional = F.Id("E");
        Formula power = F.Id("N");
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula orbit = Call("zeroOrbit", zeroData, target);
        Formula gammaI = Gamma(zeroData, i);
        Formula packet = Call(
            "convolutionSquare",
            Call("convolve", Call("convolutionSuccPower", b, power), k));

        Formula peakBound = ForAll(
            [Bound("i", Naturals())],
            Implies(
                NotMember(i, exceptional),
                And(
                    LessOrEqual(Norm(Transform(b, gammaI)), Half()),
                    LessOrEqual(
                        Norm(Transform(b, Call("conj", gammaI))), Half()))));
        Formula killerBound = ForAll(
            [Bound("i", Naturals())],
            Implies(
                And(Member(i, exceptional), NotMember(i, orbit)),
                And(
                    Equal(Transform(k, gammaI), D(0)),
                    Equal(Transform(k, Call("conj", gammaI)), D(0)))));

        Formula tailDomain = new Formula.SetBuilder(
            NotMember(j, orbit), j, Naturals());
        Formula tailIndex = Call("val", j);
        Formula tailSummand = Call(
            "zeroSummand", zeroData, packet, tailIndex);
        Formula tailLambda = Lambda(j, tailDomain, tailSummand);
        Formula summableTail = Call("Summable", tailLambda);
        Formula tailSum = Tsum(j, tailDomain, tailSummand);
        Formula majorSummand = Norm(Call(
            "zeroSummand", zeroData, Square(k), j));
        Formula majorSum = Tsum(j, Naturals(), majorSummand);
        Formula geometricFactor = new Formula.Power(
            Seq(Open, new Formula.Fraction(D(1), D(4)), Close),
            Seq(power, Sp, Plus, Sp, D(1)));
        Formula tailBound = LessOrEqual(
            Norm(tailSum),
            Multiply(geometricFactor, majorSum));
        Formula conclusion = And(summableTail, tailBound);

        return Disp(ForAll(
            [
                Bound("Z", F.Id("ZeroData")),
                Bound("n", Naturals()),
                Bound("b", F.Id("WeilTestFunction")),
                Bound("k", F.Id("WeilTestFunction")),
                Bound("E", Call("Finset", Naturals())),
                Bound("N", Naturals()),
            ],
            Implies(And(peakBound, killerBound), conclusion)));
    }

    private static Formula OffLineNonrealPremises(Formula zeroData, Formula index)
    {
        Formula zero = Call("zero", zeroData, index);
        return And(
            NotEqual(RealPart(zero), F.Id("criticalAbscissa")),
            NotEqual(ImaginaryPart(zero), D(0)));
    }

    private static Formula Gamma(Formula zeroData, Formula index) =>
        Call("gamma", zeroData, index);

    private static Formula Square(Formula test) =>
        Call("convolutionSquare", test);

    private static Formula Transform(Formula test, Formula frequency) =>
        Call("fourierLaplace", test, frequency);

    private static Formula RealPart(Formula value) =>
        Seq(Re, Sp, Open, value, Close);

    private static Formula ImaginaryPart(Formula value) =>
        Seq(Operatorname, Grp(F.Id("Im")), Sp, Open, value, Close);

    private static Formula Member(Formula value, Formula set) =>
        new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);

    private static Formula NotMember(Formula value, Formula set) =>
        new Formula.Not(Member(value, set));

    private static Formula Lambda(Formula variable, Formula domain, Formula body) =>
        Seq(Open, variable, Colon, Sp, domain, Sp, Mapsto, Sp, body, Close);

    private static Formula Tsum(Formula variable, Formula domain, Formula body) =>
        Seq(Sum, Underscore, Grp(variable, Sp, InMacro, Sp, domain), Sp, body);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Exists(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);

    private static Formula And(params Formula[] clauses)
    {
        Formula result = clauses[0];
        for (var index = 1; index < clauses.Length; index++)
        {
            result = new Formula.Logic(result, FormulaLogicOperator.And, clauses[index]);
        }

        return result;
    }

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula LessThan(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Norm(Formula value) => new Formula.Norm(value);

    private static Formula Half() => new Formula.Fraction(D(1), D(2));

    private static Formula NegativeOne() => Seq(Minus, D(1));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
