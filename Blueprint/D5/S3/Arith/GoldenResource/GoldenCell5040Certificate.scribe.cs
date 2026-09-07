using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.GoldenResource;

internal sealed class GoldenCell5040CertificateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/GoldenResource/GoldenCell5040Certificate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The golden observation fibre at 5040 has six points. Exact divisor sums and "
            + "outward rational logarithm brackets certify the strict Robin margins.",
        H("The Six-Element Golden Cell at 5040"),
        Blocks(
            Entry("goldenWeight", "golden-cell-weight", "Golden Fibonacci weights",
                GoldenWeightFormula(), DescribeRole.Definition,
                "For natural L, goldenWeight L is exactly Fib(L+2), the weight G_L in "
                    + "ZECKENDORF_EULER_5040."),
            Entry("goldenBaseExponent", "golden-cell-base-exponent", "Golden exponent window",
                GoldenBaseExponentFormula(), DescribeRole.Definition,
                "For natural a, the base exponent is Fib(greatestFib(a+1))-1. This is the "
                    + "left endpoint of the unique golden exponent window containing a."),
            Entry("goldenBaseExponent_eq_zero_iff", "golden-cell-exponent-zero",
                "The zero exponent window", ExponentZeroFormula(), DescribeRole.Theorem,
                "The zero base-exponent fibre consists only of exponent zero."),
            Entry("goldenBaseExponent_eq_one_iff", "golden-cell-exponent-one",
                "The exponent-one window", ExponentOneFormula(), DescribeRole.Theorem,
                "The base-exponent-one fibre consists only of exponent one."),
            Entry("goldenBaseExponent_eq_two_iff", "golden-cell-exponent-two",
                "The exponent-two window", ExponentTwoFormula(), DescribeRole.Theorem,
                "The base-exponent-two fibre consists exactly of exponents two and three."),
            Entry("goldenBaseExponent_eq_four_iff", "golden-cell-exponent-four",
                "The exponent-four window", ExponentFourFormula(), DescribeRole.Theorem,
                "The base-exponent-four fibre consists exactly of exponents four, five, and six."),
            Entry("goldenFactorization", "golden-cell-factorization",
                "Observed prime-exponent table", GoldenFactorizationFormula(),
                DescribeRole.Definition,
                "goldenFactorization maps goldenBaseExponent over every value of the natural "
                    + "prime factorization. The proof-irrelevant zero-preservation argument is "
                    + "omitted from the displayed computational expression."),
            Entry("goldenObservation", "golden-cell-observation", "Golden observation",
                GoldenObservationFormula(), DescribeRole.Definition,
                "goldenObservation is exactly the finite-support product of p raised to its "
                    + "goldenFactorization exponent."),
            Entry("goldenCell", "golden-cell-definition", "Golden observation cell",
                GoldenCellFormula(), DescribeRole.Definition,
                "goldenCell m is the set of positive naturals whose goldenObservation equals m."),
            Entry("goldenCellPlus", "golden-cell-positive-definition",
                "The part beyond 5040", GoldenCellPlusFormula(), DescribeRole.Definition,
                "goldenCellPlus m is exactly goldenCell m intersected with the naturals strictly "
                    + "greater than 5040. The named intersection operator denotes set intersection."),
            Entry("golden_cell_5040_identity", "golden-cell-5040-identity",
                "The six-element 5040 cell", GoldenCellIdentityFormula(), DescribeRole.Theorem,
                "This proves only the cell-identity clause of ZECKENDORF_EULER_5040 theorem 4.5. "
                    + "The divisor-language equivalences and divisor count in that theorem are "
                    + "not asserted here."),
            Entry("goldenCellPlus_finite", "golden-cell-positive-finite",
                "Every positive cell is finite", GoldenCellPlusFiniteFormula(),
                DescribeRole.Theorem,
                "Every goldenCellPlus m is finite. The proof shows each n in goldenCell m divides "
                    + "m squared by bounding each exponent by twice its observed exponent."),
            Entry("sigma_5040_cell_values", "golden-cell-5040-sigma-values",
                "Exact divisor sums on the cell", SigmaValuesFormula(), DescribeRole.Theorem,
                "Multiplicativity over the coprime prime-power factorizations gives sigma_1 values "
                    + "19344, 39312, 59520, 79248, 120960, and 243840 in cell order."),
            Entry("tripleLog", "golden-cell-triple-log", "Triple logarithm",
                TripleLogFormula(), DescribeRole.Definition,
                "tripleLog n is exactly log(log(log n)); n is coerced to the reals."),
            Entry("logSigmaRatio", "golden-cell-log-sigma-ratio",
                "Logarithmic divisor-sum ratio", LogSigmaRatioFormula(), DescribeRole.Definition,
                "logSigmaRatio n is log of sigma_1(n)/n after both naturals are coerced to reals."),
            Entry("robinLogMargin", "golden-cell-robin-log-margin",
                "Chapter-9 logarithmic Robin margin", RobinLogMarginFormula(),
                DescribeRole.Definition,
                "This is verbatim ZECKENDORF_EULER_5040 definition 9.1: Euler's constant plus "
                    + "log(log(log n)) minus log(sigma_1(n)/n)."),
            Entry("robinAdditiveMargin", "golden-cell-robin-additive-margin",
                "Additive Robin margin", RobinAdditiveMarginFormula(), DescribeRole.Definition,
                "The additive margin is sigma_1(n) times (exp(robinLogMargin n)-1), with the "
                    + "divisor sum coerced to the reals."),
            Entry("cellMinimum", "golden-cell-critical-margin",
                "Golden-cell critical margin", CellMinimumFormula(), DescribeRole.Definition,
                "cellMinimum m is the infimum of the image of robinLogMargin on goldenCellPlus m. "
                    + "For the nonempty finite cells in ZECKENDORF_EULER_5040 definition 14.1, "
                    + "cellMinimum_mem proves that this infimum is the stated minimum."),
            Entry("cellMinimum_mem", "golden-cell-critical-margin-attained",
                "The finite-cell minimum is attained", CellMinimumMemFormula(), DescribeRole.Theorem,
                "For every nonempty positive golden cell, an element realizes cellMinimum. Together "
                    + "with goldenCellPlus_finite this proves the existence clause of definition 14.1."),
            Entry("RelaxedAnalyticBracketWitness", "golden-cell-analytic-brackets",
                "The thirteen outward rational brackets", AnalyticWitnessFormula(),
                DescribeRole.Definition,
                "The proposition has exactly thirteen fields: one Euler-constant bracket and, for "
                    + "each of the six cell points, a triple-log bracket and a log-sigma-ratio "
                    + "bracket. Every endpoint is displayed as an exact real rational."),
            Entry("analytic_bracket_witness_constructed", "golden-cell-brackets-constructed",
                "Construction of all analytic leaves", ConstructedWitnessFormula(),
                DescribeRole.Theorem,
                "The thirteen bracket fields are inhabited unconditionally using the sharp "
                    + "rational logarithm expansion from RobinRationalBasis. No floating-point "
                    + "number is used."),
            Entry("robin_log_margin_5040_point_bounds", "golden-cell-5040-point-bounds",
                "Certified pointwise margins on the 5040 cell", PointBoundsFormula(),
                DescribeRole.Theorem,
                "The margin at 5040 lies in the certified outward interval from -5545/1000000 "
                    + "to -5542/1000000, and each of the other five cell points has margin "
                    + "greater than 1/100."),
            Entry("robin_log_margin_5040_bracket", "golden-cell-5040-margin-bracket",
                "Certified margin bracket at 5040", Margin5040BracketFormula(),
                DescribeRole.Theorem,
                "The certified bracket -5545/1000000 < robinLogMargin 5040 < -5542/1000000 "
                    + "is the live negative-margin input to theorem 11.2."),
            Entry("robin_log_margin_5040_cell_plus_gt", "golden-cell-5040-strong-margin",
                "The stronger positive-cell bound", StrongMarginFormula(), DescribeRole.Theorem,
                "Every n in goldenCellPlus 5040 has robinLogMargin n greater than 1/100. The "
                    + "consumer edge is theorem 11.2 below, which weakens 1/100 to 47/10000."),
            Entry("robin_log_margin_5040_cell_certificate", "golden-cell-5040-certificate",
                "Strict Robin certificate for the 5040 cell", CertificateFormula(),
                DescribeRole.Theorem,
                "This is exactly the two boxed clauses of ZECKENDORF_EULER_5040 theorem 11.2: "
                    + "the margin at 5040 is negative, while every other point of its golden cell "
                    + "has margin greater than 47/10000. The proof is unconditional."),
            Entry("cell_minimum_5040_gt_one_hundredth", "golden-cell-5040-minimum-strong",
                "Strong lower bound for the 5040 cell minimum", CellMinimumStrongFormula(),
                DescribeRole.Theorem,
                "The exact five-point minimum over goldenCellPlus 5040 exceeds 1/100."),
            Entry("cell_minimum_5040_pos", "golden-cell-5040-minimum-positive",
                "Positive critical margin at 5040", CellMinimumPositiveFormula(),
                DescribeRole.Theorem,
                "The strong minimum bound yields the requested unconditional instance "
                    + "delta_cell(5040)>0 from ZECKENDORF_EULER_5040 definition 14.1."))));

    private static DocumentBlock.Describe Entry(string declaration, string id, string title,
        Formula formula, DescribeRole role, string text) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);

    private static Formula GoldenWeightFormula()
    {
        Formula ell = F.Id("L");
        return Disp(ForAll([Bound("L", Naturals())],
            Equal(Call("goldenWeight", ell), Call("fib", Add(ell, Num(2))))));
    }

    private static Formula GoldenBaseExponentFormula()
    {
        Formula a = F.Id("a");
        Formula index = Call("greatestFib", Add(a, Num(1)));
        return Disp(ForAll([Bound("a", Naturals())], Equal(Call("goldenBaseExponent", a),
            Subtract(Call("fib", index), Num(1)))));
    }

    private static Formula ExponentZeroFormula() => ExponentIff(Num(0), Equal(F.Id("a"), Num(0)));
    private static Formula ExponentOneFormula() => ExponentIff(Num(1), Equal(F.Id("a"), Num(1)));
    private static Formula ExponentTwoFormula() => ExponentIff(Num(2),
        Or(Equal(F.Id("a"), Num(2)), Equal(F.Id("a"), Num(3))));
    private static Formula ExponentFourFormula() => ExponentIff(Num(4),
        Or(Equal(F.Id("a"), Num(4)),
            Or(Equal(F.Id("a"), Num(5)), Equal(F.Id("a"), Num(6)))));

    private static Formula ExponentIff(Formula exponent, Formula values)
    {
        Formula a = F.Id("a");
        return Disp(ForAll([Bound("a", Naturals())],
            Iff(Equal(Call("goldenBaseExponent", a), exponent), values)));
    }

    private static Formula GoldenFactorizationFormula()
    {
        Formula n = F.Id("n");
        Formula mapped = Call("mapRange", Call("factorization", n),
            F.Id("goldenBaseExponent"));
        return Disp(ForAll([Bound("n", Naturals())],
            Equal(Call("goldenFactorization", n), mapped)));
    }

    private static Formula GoldenObservationFormula()
    {
        Formula n = F.Id("n"), p = F.Id("p"), a = F.Id("a");
        Formula power = Power(p, a);
        Formula product = Call("prod", Call("goldenFactorization", n),
            Call("lambda", p, a, power));
        return Disp(ForAll([Bound("n", Naturals())],
            Equal(Call("goldenObservation", n), product)));
    }

    private static Formula GoldenCellFormula()
    {
        Formula m = F.Id("m"), n = F.Id("n");
        Formula set = SetBuilder(n, And(Lt(Num(0), n),
            Equal(Call("goldenObservation", n), m)));
        return Disp(ForAll([Bound("m", Naturals())], Equal(Cell(m), set)));
    }

    private static Formula GoldenCellPlusFormula()
    {
        Formula m = F.Id("m"), n = F.Id("n");
        Formula above = SetBuilder(n, Lt(Num(5040), n));
        return Disp(ForAll([Bound("m", Naturals())],
            Equal(CellPlus(m), Call("intersection", Cell(m), above))));
    }

    private static Formula GoldenCellIdentityFormula() => Disp(Equal(Cell(Num(5040)),
        SetLiteral(5040, 10080, 15120, 20160, 30240, 60480)));

    private static Formula GoldenCellPlusFiniteFormula()
    {
        Formula m = F.Id("m");
        return Disp(ForAll([Bound("m", Naturals())], Call("Finite", CellPlus(m))));
    }

    private static Formula SigmaValuesFormula() => Disp(AndAll(
        Equal(SigmaAt(5040), Num(19344)), Equal(SigmaAt(10080), Num(39312)),
        Equal(SigmaAt(15120), Num(59520)), Equal(SigmaAt(20160), Num(79248)),
        Equal(SigmaAt(30240), Num(120960)), Equal(SigmaAt(60480), Num(243840))));

    private static Formula TripleLogFormula()
    {
        Formula n = F.Id("n");
        return Disp(ForAll([Bound("n", Naturals())], Equal(TripleLog(n),
            Log(Log(Log(ToReal(n)))))));
    }

    private static Formula LogSigmaRatioFormula()
    {
        Formula n = F.Id("n");
        Formula ratio = Divide(ToReal(Call("sigma", Num(1), n)), ToReal(n));
        return Disp(ForAll([Bound("n", Naturals())],
            Equal(Call("logSigmaRatio", n), Log(ratio))));
    }

    private static Formula RobinLogMarginFormula()
    {
        Formula n = F.Id("n");
        Formula value = Subtract(Add(Call("eulerMascheroniConstant"), TripleLog(n)),
            Call("logSigmaRatio", n));
        return Disp(ForAll([Bound("n", Naturals())], Equal(Margin(n), value)));
    }

    private static Formula RobinAdditiveMarginFormula()
    {
        Formula n = F.Id("n");
        Formula value = Multiply(ToReal(Call("sigma", Num(1), n)),
            Parenthesized(Subtract(Call("exp", Margin(n)), Num(1))));
        return Disp(ForAll([Bound("n", Naturals())],
            Equal(Call("robinAdditiveMargin", n), value)));
    }

    private static Formula CellMinimumFormula()
    {
        Formula m = F.Id("m");
        Formula image = Call("image", F.Id("robinLogMargin"), CellPlus(m));
        return Disp(ForAll([Bound("m", Naturals())],
            Equal(Call("cellMinimum", m), Call("sInf", image))));
    }

    private static Formula CellMinimumMemFormula()
    {
        Formula m = F.Id("m"), n = F.Id("n");
        Formula attained = Exists([Bound("n", Naturals())], And(Member(n, CellPlus(m)),
            Equal(Call("cellMinimum", m), Margin(n))));
        return Disp(ForAll([Bound("m", Naturals())],
            Implies(Call("Nonempty", CellPlus(m)), attained)));
    }

    private static Formula AnalyticWitnessFormula() => Disp(Equal(
        F.Id("RelaxedAnalyticBracketWitness"), Call("structure",
            Field("gamma", GammaBracket()),
            Field("tlog5040", TripleBracket(5040, 7622169, 10000000, 762217, 1000000)),
            Field("ratio5040", RatioBracket(19344, 5040, 6724881, 5000000, 13449763, 10000000)),
            Field("tlog10080", TripleBracket(10080, 7980437, 10000000, 3990219, 5000000)),
            Field("ratio10080", RatioBracket(39312, 10080, 2721953, 2000000, 6804883, 5000000)),
            Field("tlog15120", TripleBracket(15120, 65379, 80000, 8172377, 10000000)),
            Field("ratio15120", RatioBracket(59520, 15120, 685147, 500000, 13702941, 10000000)),
            Field("tlog20160", TripleBracket(20160, 1037703, 1250000, 66413, 80000)),
            Field("ratio20160", RatioBracket(79248, 20160, 13688817, 10000000, 6844409, 5000000)),
            Field("tlog30240", TripleBracket(30240, 1694983, 2000000, 2118729, 2500000)),
            Field("ratio30240", RatioBracket(120960, 30240, 13862943, 10000000, 433217, 312500)),
            Field("tlog60480", TripleBracket(60480, 273429, 312500, 8749729, 10000000)),
            Field("ratio60480", RatioBracket(243840, 60480, 2788399, 2000000, 3485499, 2500000)))));

    private static Formula ConstructedWitnessFormula() =>
        Disp(F.Id("RelaxedAnalyticBracketWitness"));

    private static Formula PointBoundsFormula() => Disp(AndAll(
        Lt(NegativeQ(5545, 1000000), Margin(Num(5040))),
        Lt(Margin(Num(5040)), NegativeQ(5542, 1000000)),
        Lt(Q(1, 100), Margin(Num(10080))),
        Lt(Q(1, 100), Margin(Num(15120))),
        Lt(Q(1, 100), Margin(Num(20160))),
        Lt(Q(1, 100), Margin(Num(30240))),
        Lt(Q(1, 100), Margin(Num(60480)))));

    private static Formula Margin5040BracketFormula() => Disp(And(
        Lt(NegativeQ(5545, 1000000), Margin(Num(5040))),
        Lt(Margin(Num(5040)), NegativeQ(5542, 1000000))));

    private static Formula StrongMarginFormula()
    {
        Formula n = F.Id("n");
        return Disp(ForAll([Bound("n", Naturals())],
            Implies(Member(n, CellPlus(Num(5040))), Lt(Q(1, 100), Margin(n)))));
    }

    private static Formula CertificateFormula()
    {
        Formula n = F.Id("n");
        Formula cellDifference = Seq(Cell(Num(5040)), Sp, Setminus, Sp, SetLiteral(5040));
        Formula positive = ForAll([Bound("n", Naturals())],
            Implies(Member(n, cellDifference), Lt(Q(47, 10000), Margin(n))));
        return Disp(And(Lt(Margin(Num(5040)), Num(0)), positive));
    }

    private static Formula CellMinimumStrongFormula() =>
        Disp(Lt(Q(1, 100), Call("cellMinimum", Num(5040))));

    private static Formula CellMinimumPositiveFormula() =>
        Disp(Lt(Num(0), Call("cellMinimum", Num(5040))));

    private static Formula GammaBracket() => Member(Call("eulerMascheroniConstant"),
        Call("Ioo", Q(5772155, 10000000), Q(5772161, 10000000)));

    private static Formula TripleBracket(long n, long loNum, long loDen, long hiNum, long hiDen) =>
        Member(TripleLog(Num(n)), Call("Ioo", Q(loNum, loDen), Q(hiNum, hiDen)));

    private static Formula RatioBracket(long sigma, long n, long loNum, long loDen,
        long hiNum, long hiDen)
    {
        Formula ratio = Divide(ToReal(Num(sigma)), ToReal(Num(n)));
        return Member(Log(ratio), Call("Ioo", Q(loNum, loDen), Q(hiNum, hiDen)));
    }

    private static Formula Field(string name, Formula proposition) =>
        Call("field", F.Id(name), proposition);
    private static Formula Cell(Formula m) => Call("goldenCell", m);
    private static Formula CellPlus(Formula m) => Call("goldenCellPlus", m);
    private static Formula Margin(Formula n) => Call("robinLogMargin", n);
    private static Formula TripleLog(Formula n) => Call("tripleLog", n);
    private static Formula SigmaAt(long n) => Call("sigma", Num(1), Num(n));
    private static Formula Log(Formula value) => Call("log", value);
    private static Formula ToReal(Formula value) => Call("castReal", value);
    private static Formula Q(long numerator, long denominator) =>
        new Formula.Fraction(Num(numerator), Num(denominator));
    private static Formula NegativeQ(long numerator, long denominator) =>
        Seq(Minus, Q(numerator, denominator));
    private static Formula Divide(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, Parenthesized(denominator));
    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(Parenthesized(value), exponent);
    private static Formula SetBuilder(Formula value, Formula predicate) =>
        Seq(OpenBrace, value, Sp, InMacro, Sp, Naturals(), Sp, Mid, Sp, predicate, CloseBrace);
    private static Formula SetLiteral(params long[] values)
    {
        var items = new List<Formula> { OpenBrace };
        for (int i = 0; i < values.Length; i++)
        {
            if (i > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
            items.Add(Num(values[i]));
        }
        items.Add(CloseBrace);
        return Seq([.. items]);
    }
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Exists(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Member(Formula value, Formula set) =>
        new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);
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
    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Or, right);
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
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
}
