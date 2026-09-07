using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.GoldenResource;

internal sealed class RobinRationalBasisDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/GoldenResource/RobinRationalBasis.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sharp rational logarithm bounds and an exact rational checker certify the "
            + "additive Robin gap at 10080 without floating-point assumptions.",
        H("Rational Basis for the Robin Certificate"),
        Blocks(
            Entry("atanhPartial", "atanh-partial", "Truncated atanh expansion",
                AtanhPartialDefinition(), DescribeRole.Definition,
                AssessedProvenance.FromRepo(),
                "For real t and natural K, atanhPartial is twice the sum over natural j with "
                    + "0 <= j < K of t^(2j+1)/(2j+1). The denominator is coerced to the reals. "
                    + "This is the defining expression in the ZECKENDORF_EULER_5040 appendix."),
            Entry("atanhParameter", "atanh-parameter", "Atanh reduction parameter",
                AtanhParameterDefinition(), DescribeRole.Definition,
                AssessedProvenance.FromRepo(),
                "For real y, atanhParameter is exactly (y-1)/(y+1), as stated in the "
                    + "ZECKENDORF_EULER_5040 appendix."),
            Entry("atanhParameter_lt_third", "atanh-parameter-lt-third",
                "Atanh parameter interval", AtanhParameterBoundsFormula(), DescribeRole.Theorem,
                AssessedProvenance.FromRepo(),
                "For 1 <= y < 2, the appendix parameter is nonnegative and strictly less than "
                    + "1/3. This elementary estimate is stated as in the "
                    + "ZECKENDORF_EULER_5040 appendix."),
            Entry("logRemainder", "log-remainder", "Named logarithm remainder",
                LogRemainderDefinition(), DescribeRole.Definition,
                AssessedProvenance.FromRepo(),
                "For real y and natural K, logRemainder is exactly log y minus the truncated "
                    + "atanh series evaluated at atanhParameter y."),
            Entry("log_expansion_remainder_bound", "log-expansion-remainder-bound",
                "Sharp logarithm expansion remainder", LogExpansionFormula(), DescribeRole.Theorem,
                AssessedProvenance.FromRepo(),
                "For 1 <= y < 2, substitute t=(y-1)/(y+1). The logarithm exceeds the finite "
                    + "sum by a nonnegative remainder bounded by 2t^(2K+1)/((2K+1)(1-t^2)). "
                    + "The sharp factor 1/(2K+1) is proved by an integral majorant. This is the "
                    + "first boxed statement of the ZECKENDORF_EULER_5040 appendix and an "
                    + "elementary atanh-series remainder estimate stated there."),
            Entry("log_harmonic_term_bounds", "log-harmonic-term-bounds",
                "Termwise logarithmic estimate", HarmonicTermFormula(), DescribeRole.Theorem,
                AssessedProvenance.FromRepo(),
                "For positive real x, the displayed strict two-sided estimate bounds "
                    + "log((x+1)/x)-1/(x+1). It is the elementary appendix estimate used to "
                    + "prove A.1, stated as in ZECKENDORF_EULER_5040."),
            Entry("eulerMascheroni_remainder_bounds", "euler-mascheroni-remainder-bounds",
                "Euler--Mascheroni remainder bracket A.1", EulerRemainderFormula(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(),
                "For every natural N >= 1, this is exactly equation (A.1) of the "
                    + "ZECKENDORF_EULER_5040 appendix. The proof squeezes strictly monotone and "
                    + "antitone corrected harmonic sequences to the Euler--Mascheroni constant; "
                    + "this elementary harmonic-asymptotic estimate is stated as in that appendix."),
            Entry("log_two_decimal_bounds", "log-two-decimal-bounds",
                "Pinned decimal bounds for log 2", LogTwoFormula(), DescribeRole.Theorem,
                AssessedProvenance.FromRepo(),
                "This companion records the two certified Mathlib decimal inequalities for log 2. "
                    + "Its consumer is eulerMascheroni_decimal_bounds through the logarithm-of-1000 calculation."),
            Entry("eulerMascheroni_decimal_bounds", "euler-mascheroni-decimal-bounds",
                "Decimal Euler--Mascheroni bracket", EulerDecimalFormula(), DescribeRole.Theorem,
                AssessedProvenance.FromRepo(),
                "The N=1000 specialization of A.1, together with the sharp logarithm expansion, "
                    + "proves 0.5772155 < gamma_EM < 0.5772161 in the Lean kernel."),
            Entry("RationalBracket", "rational-bracket", "Rational interval data",
                RationalBracketFormula(), DescribeRole.Definition,
                AssessedProvenance.FromRepo(),
                "RationalBracket is a structure with rational fields lower and upper. It is data; "
                    + "endpoint order and semantic containment are checked separately."),
            Entry("Contains", "rational-bracket-contains",
                "Semantic bracket containment", ContainsFormula(), DescribeRole.Definition,
                AssessedProvenance.FromRepo(),
                "Contains b x means that the rational endpoints b.lower and b.upper, each coerced "
                    + "to the reals, enclose x with non-strict inequalities."),
            Entry("expPartial", "exp-partial", "Truncated rational exponential",
                ExpPartialFormula(), DescribeRole.Definition,
                AssessedProvenance.FromRepo(),
                "For rational q and natural term count, expPartial is Mathlib's exponential "
                    + "formal-series partial sum evaluated at q."),
            Entry("expPartial_eq_sum", "exp-partial-eq-sum",
                "Finite-sum form of the exponential partial sum", ExpPartialSumFormula(),
                DescribeRole.Theorem, AssessedProvenance.FromRepo(),
                "The Mathlib formal-series wrapper equals the rational indexed sum over natural "
                    + "i in range terms of q^i/i!."),
            Entry("robinDelta", "robin-delta", "Additive Robin gap",
                RobinDeltaFormula(), DescribeRole.Definition,
                AssessedProvenance.FromRepo(),
                "The additive Robin gap exp(gamma_EM) times n times log(log n), minus sigma_1(n), "
                    + "is an auxiliary quantity of this module. The volume's chapter-9 margin "
                    + "Delta(n) = gamma_EM + log(log(log n)) - log(sigma_1(n)/n) is a different "
                    + "(logarithmic) quantity, formalized in the companion module "
                    + "GoldenCell5040Certificate. Only the signs of the two agree, and no identity "
                    + "between them is claimed here. Its exact rational basis follows "
                    + "「ZECKENDORF_EULER_5040 附录」."),
            Entry("RobinPositiveJudge", "robin-positive-judge", "Rational positivity predicate",
                RobinJudgeFormula(), DescribeRole.Definition,
                AssessedProvenance.FromRepo(),
                "This module's own auxiliary judge for the additive Robin gap checks ordered gamma "
                    + "and log-log brackets, nonnegative lower endpoints, and one strict rational "
                    + "inequality. sigma_1(n) and n are coerced to rationals. Its exact rational "
                    + "basis follows 「ZECKENDORF_EULER_5040 附录」; no floating-point value enters "
                    + "this predicate."),
            Entry("robinPositiveJudgeDecidable", "robin-positive-judge-decidable",
                "Decidability of the rational judge", JudgeDecidableFormula(), DescribeRole.Definition,
                AssessedProvenance.FromRepo(),
                "For every natural input and rational bracket pair, the checker predicate has the "
                    + "explicitly named Decidable instance robinPositiveJudgeDecidable."),
            Entry("robinPositiveJudge_sound", "robin-positive-judge-sound",
                "Soundness of the rational checker", JudgeSoundFormula(), DescribeRole.Theorem,
                AssessedProvenance.FromRepo(),
                "Valid semantic brackets and this module's own auxiliary judge imply positivity of "
                    + "the additive Robin gap. The proof lower-bounds exp(gamma_EM) by the truncated "
                    + "Taylor sum from the exact rational basis in 「ZECKENDORF_EULER_5040 附录」 "
                    + "and uses monotonicity. This is the general result named by the checker utility "
                    + "record, not an identity with the volume's logarithmic margin."),
            Entry("log_pow_two_mul_bounds", "log-pow-two-mul-bounds",
                "Logarithm bounds after binary scaling", LogPowTwoFormula(), DescribeRole.Theorem,
                AssessedProvenance.FromRepo(),
                "For positive natural k and 1 <= y < 2, the appendix log-2 bracket and sharp "
                    + "atanh remainder give the displayed enclosure of log(2^k y)."),
            Entry("rational_log_bounds", "rational-log-bounds",
                "Transfer a checked atanh calculation", RationalLogTransferFormula(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(),
                "An exact identity x=2^k y and a checked pair of rational endpoint inequalities "
                    + "transfer to lo < log x < hi. This public helper is consumed by module 2."),
            Entry("log_interval_bounds", "log-interval-bounds",
                "Transfer logarithm endpoint bounds", LogIntervalFormula(), DescribeRole.Theorem,
                AssessedProvenance.FromRepo(),
                "For 0<a<x<b, a certified lower bound for log a and upper bound for log b "
                    + "transfer across strict monotonicity of the real logarithm."),
            Entry("log_10080_bounds", "log-10080-bounds",
                "Rational bounds for log 10080", Log10080Formula(), DescribeRole.Theorem,
                AssessedProvenance.FromRepo(),
                "The public exact-rational calculation encloses log 10080 between the displayed endpoints."),
            Entry("logLog_10080_bounds", "log-log-10080-bounds",
                "Rational bounds for log log 10080", LogLog10080Formula(), DescribeRole.Theorem,
                AssessedProvenance.FromRepo(),
                "The public interval transfer encloses log(log 10080); its endpoints are those "
                    + "stored in logLog10080Bracket."),
            Entry("gammaBracket", "gamma-bracket", "Concrete gamma checker input",
                GammaBracketFormula(), DescribeRole.Definition,
                AssessedProvenance.FromRepo(),
                "gammaBracket is exactly the pair 5772155/10000000 and 5772161/10000000."),
            Entry("logLog10080Bracket", "log-log-10080-bracket",
                "Concrete log-log checker input", LogLogBracketFormula(), DescribeRole.Definition,
                AssessedProvenance.FromRepo(),
                "logLog10080Bracket is exactly the pair 55529789/25000000 and "
                    + "222119157/100000000."),
            Entry("robin_positive_judge_10080", "robin-positive-judge-10080",
                "First exact checker computation", Judge10080Formula(), DescribeRole.Theorem,
                AssessedProvenance.FromRepo(),
                "Kernel reduction proves that four exponential terms make the rational checker "
                    + "true at n=10080. The exact divisor sum sigma_1(10080)=39312 is proved privately."),
            Entry("robin_delta_10080_pos", "robin-delta-10080-positive",
                "Positive additive Robin gap at 10080", Delta10080Formula(), DescribeRole.Theorem,
                AssessedProvenance.FromRepo(),
                "Checker soundness, the two semantic brackets, and the decided four-term input from "
                    + "the exact rational basis in 「ZECKENDORF_EULER_5040 附录」 prove that this "
                    + "module's own auxiliary additive Robin gap is positive at 10080 without "
                    + "floating point; this is not an identity with the volume's logarithmic margin."))));

    private static DocumentBlock.Describe Entry(string declaration, string id, string title,
        Formula formula, DescribeRole role, AssessedProvenance provenance, string text) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(text))), role);

    private static Formula AtanhPartialDefinition()
    {
        Formula t = F.Id("t");
        Formula k = F.Id("K");
        return Disp(ForAll([Bound("t", Reals()), Bound("K", Naturals())],
            Equal(Partial(t, k), Multiply(Num(2), IndexedSum(F.Id("j"), k,
                Divide(Power(t, Odd(F.Id("j"))), ToReal(Odd(F.Id("j")))))))));
    }

    private static Formula AtanhParameterDefinition()
    {
        Formula y = F.Id("y");
        return Disp(ForAll([Bound("y", Reals())],
            Equal(AtanhParameter(y), Divide(Subtract(y, Num(1)), Add(y, Num(1))))));
    }

    private static Formula AtanhParameterBoundsFormula()
    {
        Formula y = F.Id("y");
        Formula parameter = AtanhParameter(y);
        return Disp(ForAll([Bound("y", Reals())],
            Implies(And(Le(Num(1), y), Lt(y, Num(2))),
                And(Le(Num(0), parameter), Lt(parameter, Q(1, 3))))));
    }

    private static Formula LogRemainderDefinition()
    {
        Formula y = F.Id("y");
        Formula k = F.Id("K");
        return Disp(ForAll([Bound("y", Reals()), Bound("K", Naturals())],
            Equal(LogRemainder(y, k), Subtract(Log(y), Partial(AtanhParameter(y), k)))));
    }

    private static Formula LogExpansionFormula()
    {
        Formula y = F.Id("y");
        Formula k = F.Id("K");
        Formula t = AtanhParameter(y);
        Formula error = LogRemainder(y, k);
        return Disp(ForAll([Bound("y", Reals()), Bound("K", Naturals())],
            Implies(And(Le(Num(1), y), Lt(y, Num(2))),
                And(Le(Num(0), error), Le(error, Remainder(t, k))))));
    }

    private static Formula HarmonicTermFormula()
    {
        Formula x = F.Id("x");
        Formula xp = Add(x, Num(1));
        Formula center = Subtract(Log(Divide(xp, x)), Divide(Num(1), xp));
        return Disp(ForAll([Bound("x", Reals())], Implies(Lt(Num(0), x),
            And(Lt(Divide(Num(1), Multiply(Num(2), Power(Parenthesized(xp), Num(2)))), center),
                Lt(center, Divide(Num(1), Multiply(Multiply(Num(2), x), xp)))))));
    }

    private static Formula EulerRemainderFormula()
    {
        Formula n = F.Id("N");
        Formula center = Subtract(Subtract(ToReal(Call("harmonic", n)), Log(ToReal(n))), Gamma());
        return Disp(ForAll([Bound("N", Naturals())], Implies(Le(Num(1), n),
            And(Lt(Divide(Num(1), Multiply(Num(2), ToReal(Add(n, Num(1))))), center),
                Lt(center, Divide(Num(1), Multiply(Num(2), ToReal(n))))))));
    }

    private static Formula LogTwoFormula() => Disp(And(
        Lt(Q(6931471803, 10000000000), Log(Num(2))),
        Lt(Log(Num(2)), Q(6931471808, 10000000000))));

    private static Formula EulerDecimalFormula() => Disp(And(
        Lt(Q(5772155, 10000000), Gamma()), Lt(Gamma(), Q(5772161, 10000000))));

    private static Formula RationalBracketFormula() => Disp(Equal(F.Id("RationalBracket"),
        Call("structure", Call("lower", Rationals()), Call("upper", Rationals()))));

    private static Formula ContainsFormula()
    {
        Formula b = F.Id("b");
        Formula x = F.Id("x");
        return Disp(ForAll([Bound("b", F.Id("RationalBracket")), Bound("x", Reals())],
            Iff(Call("Contains", b, x), And(Le(ToReal(Lower(b)), x), Le(x, ToReal(Upper(b)))))));
    }

    private static Formula ExpPartialFormula()
    {
        Formula q = F.Id("q");
        Formula terms = F.Id("terms");
        return Disp(ForAll([Bound("q", Rationals()), Bound("terms", Naturals())],
            Equal(Call("expPartial", q, terms),
                Call("partialSum", Call("expSeries", Rationals(), Rationals()), terms, q))));
    }

    private static Formula ExpPartialSumFormula()
    {
        Formula q = F.Id("q");
        Formula terms = F.Id("terms");
        Formula i = F.Id("i");
        return Disp(ForAll([Bound("q", Rationals()), Bound("terms", Naturals())],
            Equal(Call("expPartial", q, terms),
                IndexedSum(i, terms, Divide(Power(q, i), ToRat(Call("factorial", i)))))));
    }

    private static Formula RobinDeltaFormula()
    {
        Formula n = F.Id("n");
        Formula value = Subtract(Multiply(Multiply(Call("exp", Gamma()), ToReal(n)),
            Log(Log(ToReal(n)))), ToReal(Call("sigma", Num(1), n)));
        return Disp(ForAll([Bound("n", Naturals())], Equal(Call("robinDelta", n), value)));
    }

    private static Formula RobinJudgeFormula()
    {
        Formula n = F.Id("n");
        Formula terms = F.Id("terms");
        Formula gamma = F.Id("gamma");
        Formula logLog = F.Id("logLog");
        Formula certificate = Lt(ToRat(Call("sigma", Num(1), n)),
            Multiply(Multiply(Call("expPartial", Lower(gamma), terms), ToRat(n)), Lower(logLog)));
        Formula body = AndAll(Le(Lower(gamma), Upper(gamma)), Le(Lower(logLog), Upper(logLog)),
            Le(Num(0), Lower(gamma)), Le(Num(0), Lower(logLog)), certificate);
        return Disp(ForAll(JudgeBounds(), Iff(Call("RobinPositiveJudge", n, terms, gamma, logLog), body)));
    }

    private static Formula JudgeDecidableFormula()
    {
        Formula n = F.Id("n");
        Formula terms = F.Id("terms");
        Formula gamma = F.Id("gamma");
        Formula logLog = F.Id("logLog");
        return Disp(ForAll(JudgeBounds(),
            Call("Decidable", Call("RobinPositiveJudge", n, terms, gamma, logLog))));
    }

    private static Formula JudgeSoundFormula()
    {
        Formula n = F.Id("n");
        Formula terms = F.Id("terms");
        Formula gamma = F.Id("gamma");
        Formula logLog = F.Id("logLog");
        Formula premises = AndAll(Call("Contains", gamma, Gamma()),
            Call("Contains", logLog, Log(Log(ToReal(n)))),
            Call("RobinPositiveJudge", n, terms, gamma, logLog));
        return Disp(ForAll(JudgeBounds(), Implies(premises, Lt(Num(0), Call("robinDelta", n)))));
    }

    private static Formula LogPowTwoFormula()
    {
        Formula y = F.Id("y");
        Formula k = F.Id("k");
        Formula cap = F.Id("K");
        Formula t = Divide(Subtract(y, Num(1)), Add(y, Num(1)));
        Formula target = Log(Multiply(Power(Num(2), k), y));
        return Disp(ForAll([Bound("y", Reals()), Bound("k", Naturals()), Bound("K", Naturals())],
            Implies(AndAll(Le(Num(1), k), Le(Num(1), y), Lt(y, Num(2))),
                And(Lt(LogLower(y, k, cap), target), Lt(target, LogUpper(y, k, cap))))));
    }

    private static Formula RationalLogTransferFormula()
    {
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula lo = F.Id("lo");
        Formula hi = F.Id("hi");
        Formula k = F.Id("k");
        Formula cap = F.Id("K");
        Formula premises = AndAll(Equal(x, Multiply(Power(Num(2), k), y)), Le(Num(1), k),
            Le(Num(1), y), Lt(y, Num(2)),
            And(Lt(lo, LogLower(y, k, cap)), Lt(LogUpper(y, k, cap), hi)));
        return Disp(ForAll([
            Bound("x", Reals()), Bound("y", Reals()), Bound("lo", Reals()), Bound("hi", Reals()),
            Bound("k", Naturals()), Bound("K", Naturals())],
            Implies(premises, And(Lt(lo, Log(x)), Lt(Log(x), hi)))));
    }

    private static Formula LogIntervalFormula()
    {
        Formula x = F.Id("x");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula lo = F.Id("lo");
        Formula hi = F.Id("hi");
        Formula premises = AndAll(Lt(Num(0), a), Lt(a, x), Lt(x, b), Lt(lo, Log(a)), Lt(Log(b), hi));
        return Disp(ForAll([
            Bound("x", Reals()), Bound("a", Reals()), Bound("b", Reals()),
            Bound("lo", Reals()), Bound("hi", Reals())],
            Implies(premises, And(Lt(lo, Log(x)), Lt(Log(x), hi)))));
    }

    private static Formula Log10080Formula() => Disp(And(
        Lt(Q(921830853, 100000000), Log(Num(10080))),
        Lt(Log(Num(10080)), Q(184366171, 20000000))));

    private static Formula LogLog10080Formula() => Disp(And(
        Lt(Q(55529789, 25000000), Log(Log(Num(10080)))),
        Lt(Log(Log(Num(10080))), Q(222119157, 100000000))));

    private static Formula GammaBracketFormula() => Disp(Equal(F.Id("gammaBracket"),
        Call("RationalBracket", Q(5772155, 10000000), Q(5772161, 10000000))));

    private static Formula LogLogBracketFormula() => Disp(Equal(F.Id("logLog10080Bracket"),
        Call("RationalBracket", Q(55529789, 25000000), Q(222119157, 100000000))));

    private static Formula Judge10080Formula() => Disp(Call("RobinPositiveJudge",
        Num(10080), Num(4), F.Id("gammaBracket"), F.Id("logLog10080Bracket")));

    private static Formula Delta10080Formula() => Disp(Lt(Num(0), Call("robinDelta", Num(10080))));

    private static Formula LogLower(Formula y, Formula k, Formula cap)
    {
        Formula t = Divide(Subtract(y, Num(1)), Add(y, Num(1)));
        return Add(Multiply(ToReal(k), Q(6931471803, 10000000000)), Partial(t, cap));
    }

    private static Formula LogUpper(Formula y, Formula k, Formula cap)
    {
        Formula t = Divide(Subtract(y, Num(1)), Add(y, Num(1)));
        return Add(Add(Multiply(ToReal(k), Q(6931471808, 10000000000)), Partial(t, cap)),
            Remainder(t, cap));
    }

    private static Formula Remainder(Formula t, Formula k) => Divide(
        Multiply(Num(2), Power(Parenthesized(t), Odd(k))),
        Multiply(ToReal(Odd(k)), Subtract(Num(1), Power(Parenthesized(t), Num(2)))));

    private static Formula Partial(Formula t, Formula k) => Call("atanhPartial", t, k);
    private static Formula AtanhParameter(Formula y) => Call("atanhParameter", y);
    private static Formula LogRemainder(Formula y, Formula k) => Call("logRemainder", y, k);
    private static Formula Gamma() => Call("eulerMascheroniConstant");
    private static Formula Lower(Formula bracket) => Call("lower", bracket);
    private static Formula Upper(Formula bracket) => Call("upper", bracket);
    private static Formula Log(Formula value) => Call("log", value);
    private static Formula Odd(Formula value) => Add(Multiply(Num(2), value), Num(1));
    private static Formula IndexedSum(Formula index, Formula bound, Formula term) =>
        Seq(new Formula.Subscript(Sum,
            Seq(index, Sp, InMacro, Sp, Call("range", bound))), Sp, Parenthesized(term));
    private static Formula Q(long numerator, long denominator) =>
        new Formula.Fraction(Num(numerator), Num(denominator));
    private static Formula Divide(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, Parenthesized(denominator));
    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(Parenthesized(value), exponent);
    private static Formula ToReal(Formula value) => Call("castReal", value);
    private static Formula ToRat(Formula value) => Call("castRat", value);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
    private static Formula.BoundVariable[] JudgeBounds() => [
        Bound("n", Naturals()), Bound("terms", Naturals()),
        Bound("gamma", F.Id("RationalBracket")), Bound("logLog", F.Id("RationalBracket"))];
    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula AndAll(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (int i = clauses.Length - 2; i >= 0; i--)
        {
            result = And(clauses[i], result);
        }
        return result;
    }
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Rationals() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
}
