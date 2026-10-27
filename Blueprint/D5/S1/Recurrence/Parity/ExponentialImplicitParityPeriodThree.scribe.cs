using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Parity;

internal sealed class ExponentialImplicitParityPeriodThreeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The implicit exponential generating function of OEIS A392208 has coefficient parity of period three.",
        H("OEIS A392208: Parity Has Period Three"),
        Blocks(
            Node("a392208-published-egfone", "egfOne", "egfOne",
                PublishedFormula("egfOne"), "The displayed formula gives the coefficient operation or identity with all parameters quantified.",
                AssessedProvenance.FromRepo(), DescribeRole.Definition),
            Node("a392208-published-egfpow-congr-at", "egfPow_congr_at", "egfPow congr at",
                PublishedFormula("egfPow_congr_at"), "The displayed formula gives the coefficient operation or identity with all parameters quantified.",
                AssessedProvenance.FromRepo(), DescribeRole.Theorem),
            Node("a392208-published-egfseries-mul", "egfSeries_mul", "egfSeries mul",
                PublishedFormula("egfSeries_mul"), "The displayed formula gives the coefficient operation or identity with all parameters quantified.",
                AssessedProvenance.FromRepo(), DescribeRole.Theorem),
            Node("a392208-published-egfseries-pow", "egfSeries_pow", "egfSeries pow",
                PublishedFormula("egfSeries_pow"), "The displayed formula gives the coefficient operation or identity with all parameters quantified.",
                AssessedProvenance.FromRepo(), DescribeRole.Theorem),
            Node("a392208-published-egfcoeffs", "egfCoeffs", "egfCoeffs",
                PublishedFormula("egfCoeffs"), "The displayed formula gives the coefficient operation or identity with all parameters quantified.",
                AssessedProvenance.FromRepo(), DescribeRole.Definition),
            Node("a392208-published-egfseries-egfcoeffs", "egfSeries_egfCoeffs", "egfSeries egfCoeffs",
                PublishedFormula("egfSeries_egfCoeffs"), "The displayed formula gives the coefficient operation or identity with all parameters quantified.",
                AssessedProvenance.FromRepo(), DescribeRole.Theorem),
            Paragraph(Text("OEIS A392208 (entry dated 2026-01-24) supplies the defining equation "
                + "A'(x) = exp(A(x) A'(x)^3) and the conjecture that a(n) is even if and only if "
                + "3 divides n for n >= 1. The entry supplies context rather than the repository's "
                + "strengthened integer recurrence, ODE uniqueness theorem, period-three proof, or theorem "
                + "quantified over every integer sequence satisfying the equation.")),
            Node("a392208-egf-mul", "egfMul", "Binomial convolution", EgfMulFormula(),
                "OEIS A392208 (2026-01-24) uses exponential generating functions. This definition is "
                    + "the binomial convolution whose nth value is the displayed finite sum; range(n+1) "
                    + "contains exactly 0 through n, and natural subtraction in n-k is truncated at zero.",
                AssessedProvenance.FromRepo(), DescribeRole.Definition),
            Node("a392208-egf-pow", "egfPow", "Iterated binomial convolution", EgfPowFormula(),
                "OEIS A392208 (2026-01-24) contains the third and fifth powers of the derivative. "
                    + "The zero convolution power is the sequence that is one at zero and zero elsewhere; "
                    + "the successor clause is left binomial convolution by f.",
                AssessedProvenance.FromRepo(), DescribeRole.Definition),
            Node("a392208-recurrence-rhs", "recurrenceRhs", "Recursive next-coefficient expression",
                RecurrenceRhsFormula(),
                "The repository defines this integer expression to append the next triangular recurrence "
                    + "coefficient. OEIS A392208 (2026-01-24) supplies context through its defining equation; "
                    + "this explicit integer recurrence expression is a repository strengthening beyond the "
                    + "OEIS wording.", AssessedProvenance.FromRepo(), DescribeRole.Definition),
            Node("a392208-table", "table", "Finite recursive coefficient table", TableFormula(),
                "The public table starts with the exact list [0,1]. At the successor step it appends exactly "
                    + "one value of recurrenceRhs, evaluated on getD of the preceding table with default zero. "
                    + "This repository object makes the definition of a self-contained.",
                AssessedProvenance.FromRepo(), DescribeRole.Definition),
            Node("a392208-sequence", "a", "The recurrence-defined integer sequence", SequenceFormula(),
                "OEIS A392208 (2026-01-24) supplies the initial coefficients 0,1 for A itself. The public "
                    + "finite table starts at [0,1], appends the triangular recurrence value at every step, "
                    + "and getD returns zero only outside that table; the displayed clauses are the literal "
                    + "definition of a. The next theorem exports its recurrence without the auxiliary table.",
                AssessedProvenance.FromRepo(), DescribeRole.Definition),
            Node("a392208-initial-residues", "initial_residues_mod_two", "Initial residues modulo two",
                InitialResiduesFormula(),
                "The recurrence-defined sequence has the right-associated initial residue triple (0,1,1) "
                    + "in ZMod(2), exactly as named in the candidate theorem atom.",
                AssessedProvenance.FromRepo(), DescribeRole.Theorem),
            Node("a392208-recurrence", "a_recurrence", "Triangular integer recurrence", RecurrenceFormula(),
                "The ODE obtained from OEIS A392208 (2026-01-24) gives this integer recurrence. The apparent "
                    + "top second-derivative coefficient in the second summand vanishes because a(0)=0, so "
                    + "the recurrence is triangular with leading coefficient one.",
                AssessedProvenance.FromRepo(), DescribeRole.Theorem),
            Node("a392208-recurrence-period", "recurrence_coefficient_period_three",
                "Period three modulo two", RecurrencePeriodFormula(),
                "For the recurrence-defined sequence attached to OEIS A392208 (2026-01-24), every coefficient "
                    + "three places later is congruent modulo two. ModEqZ denotes integer congruence, not a cast "
                    + "or rational equality.", AssessedProvenance.FromRepo(), DescribeRole.Theorem),
            Node("a392208-exp-defines", "ExpDefines", "Implicit exponential power-series equation",
                ExpDefinesFormula(),
                "This is the exact formal power-series equation from OEIS A392208 (2026-01-24), together with "
                    + "A(0)=0. DQ is formal differentiation over the rationals, expQ is the rational formal "
                    + "exponential series, and subst is formal substitution.",
                AssessedProvenance.FromRepo(), DescribeRole.Definition),
            Node("a392208-exp-implies-ode", "exp_definition_implies_ode",
                "The implicit equation implies the ODE", ExpImpliesOdeFormula(),
                "Differentiating the equation in OEIS A392208 (2026-01-24) with the formal substitution chain "
                    + "rule yields the displayed denominator-free ODE. No analytic convergence is assumed.",
                AssessedProvenance.FromRepo(), DescribeRole.Theorem),
            Node("a392208-egf-series", "egfSeries", "Rational exponential generating series",
                EgfSeriesFormula(),
                "For OEIS A392208 (2026-01-24), the ordinary coefficient of x^n is s(n)/n!. The displayed "
                    + "fraction is rational division; no natural-number or integer division is used.",
                AssessedProvenance.FromRepo(), DescribeRole.Definition),
            Node("a392208-first-derivative", "exp_definition_derivative_zero",
                "The first derivative has constant coefficient one", FirstDerivativeFormula(),
                "Evaluating the defining equation at constant coefficient zero yields A'(0)=1, which the "
                    + "identification of the OEIS-defined sequence with the recurrence uses.",
                AssessedProvenance.FromRepo(), DescribeRole.Theorem),
            Node("a392208-egf-ode", "EgfOde", "Coefficient form of the ODE", EgfOdeFormula(),
                "This is the coefficient recurrence for the ODE derived from OEIS A392208 (2026-01-24), "
                    + "written over rational sequences using the public binomial convolution operations.",
                AssessedProvenance.FromRepo(), DescribeRole.Definition),
            Node("a392208-egf-ode-unique", "egfOde_unique", "Uniqueness of the coefficient ODE",
                EgfOdeUniqueFormula(),
                "For OEIS A392208 (2026-01-24), two rational coefficient sequences satisfying the same "
                    + "triangular ODE recurrence and initial coefficients 0,1 agree everywhere. Strong induction "
                    + "uses the vanished top coefficient in the nonlinear term.",
                AssessedProvenance.FromRepo(), DescribeRole.Theorem),
            Node("a392208-oeis-defines", "OEISDefines", "Exact OEIS integer-sequence predicate",
                OeisDefinesFormula(),
                "This expands the defining expression from OEIS A392208 (2026-01-24): castQ maps every integer "
                    + "coefficient to the rationals before forming its EGF, whose constant coefficient is zero "
                    + "and whose derivative is the substituted exponential shown here.",
                AssessedProvenance.FromRepo(), DescribeRole.Definition),
            Node("a392208-a-oeis-defines", "a_oeisDefines",
                "The recurrence sequence satisfies the OEIS equation", OeisWitnessFormula(),
                "The named witness connects the repository sequence a to the exact generating-function "
                    + "predicate from OEIS A392208 (2026-01-24). Its proof follows the integer recurrence through "
                    + "the rational coefficient ODE and reconstructs the implicit exponential equation.",
                AssessedProvenance.FromRepo(), DescribeRole.Theorem),
            Node("a392208-identification", "oeis_defined_eq_recurrence",
                "The OEIS equation determines the recurrence sequence", IdentificationFormula(),
                "Every integer sequence satisfying the exact equation of OEIS A392208 (2026-01-24) equals a. "
                    + "The proof derives the ODE and A'(0)=1, applies triangular uniqueness over the rationals, "
                    + "and then recovers equality of the integer coefficients.",
                AssessedProvenance.FromRepo(), DescribeRole.Theorem),
            Node("a392208-oeis-period", "oeis_coefficient_period_three",
                "Every OEIS-defined sequence has period three modulo two", OeisPeriodFormula(),
                "Identification with a transfers the kernel-verified period-three congruence to every integer "
                    + "sequence satisfying OEIS A392208 (2026-01-24).",
                AssessedProvenance.FromRepo(), DescribeRole.Theorem),
            Node("a392208-parity-of-oeis-defines", "parity_conjecture_of_oeisDefines",
                "Every OEIS-defined sequence satisfies the parity law", ConditionalParityFormula(),
                "This public companion transfers the parity theorem for a to every integer sequence satisfying "
                    + "the exact OEIS A392208 (2026-01-24) equation. It remains conditional on that defining "
                    + "predicate and is distinct from the unconditional atom anchor.",
                AssessedProvenance.FromRepo(), DescribeRole.Theorem),
            Node("a392208-parity-conjecture", "a392208_parity_conjecture",
                "The A392208 parity conjecture", ParityFormula(),
                "This is the unconditional atom clause for the repository sequence a: at every positive index, "
                    + "a(n) is even if and only if three divides n. Its live proof specializes the general "
                    + "OEIS-defined parity theorem with the named witness a_oeisDefines.",
                AssessedProvenance.FromRepo(), DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, Formula formula,
        string prose, AssessedProvenance provenance, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula EgfMulFormula()
    {
        Formula r = F.Id("R"), f = F.Id("f"), g = F.Id("g"), n = F.Id("n"), k = F.Id("k");
        Formula summand = Mul(Mul(Call("choose", n, k), Call("f", k)), Call("g", Sub(n, k)));
        return Disp(Seq(Forall, Sp, Typed(r, F.Id("Type")), Comma, Sp,
            Parenthesized(Call("CommSemiring", r)), Comma, Sp,
            Typed(f, Arrow(Naturals(), r)), Comma, Sp, Typed(g, Arrow(Naturals(), r)), Comma, Sp,
            Typed(n, Naturals()), Comma, Sp,
            Equal(Call("egfMul", f, g, n), FiniteSum(k, Call("range", Add(n, D(1))), summand))));
    }

    private static Formula EgfPowFormula()
    {
        Formula r = F.Id("R"), f = F.Id("f"), m = F.Id("m"), n = F.Id("n");
        Formula zeroValue = Call("ite", Equal(n, D(0)), D(1), D(0));
        Formula baseClause = Equal(Call("egfPow", f, D(0), n), zeroValue);
        Formula stepClause = Seq(Forall, Sp, Typed(m, Naturals()), Comma, Sp,
            Equal(Call("egfPow", f, Add(m, D(1)), n),
                Call("egfMul", f, Call("egfPow", f, m), n)));
        return Disp(Seq(Forall, Sp, Typed(r, F.Id("Type")), Comma, Sp,
            Parenthesized(Call("CommSemiring", r)), Comma, Sp,
            Typed(f, Arrow(Naturals(), r)), Comma, Sp, Typed(n, Naturals()), Comma, Sp,
            Conjoin(baseClause, stepClause)));
    }

    private static Formula RecurrenceRhsFormula()
    {
        Formula s = F.Id("s"), n = F.Id("n"), j = F.Id("j");
        Formula s1 = LambdaAt(j, Call("s", Add(j, D(1))));
        Formula prefix = LambdaAt(j, Call("ite",
            new Formula.Relation(j, FormulaRelationOperator.LessThan, n),
            Call("s", Add(j, D(2))), D(0)));
        Formula rhs = Add(Call("egfPow", s1, D(5), n), Mul(D(3),
            Call("egfMul", Call("egfMul", s, Call("egfPow", s1, D(3))), prefix, n)));
        return Disp(Seq(Forall, Sp, Typed(s, Arrow(Naturals(), Integers())), Comma, Sp,
            Typed(n, Naturals()), Comma, Sp, Equal(Call("recurrenceRhs", s, n), rhs)));
    }

    private static Formula TableFormula()
    {
        Formula n = F.Id("n"), k = F.Id("k"), xs = Call("table", n);
        Formula prior = LambdaAt(k, Call("getD", xs, k, D(0)));
        Formula baseClause = Equal(Call("table", D(0)), List(D(0), D(1)));
        Formula stepClause = Seq(Forall, Sp, Typed(n, Naturals()), Comma, Sp,
            Equal(Call("table", Add(n, D(1))),
                Call("append", xs, List(Call("recurrenceRhs", prior, n)))));
        return Disp(new Formula.Aligned([
            Seq(F.Id("table"), Colon, Sp, Arrow(Naturals(), Call("List", Integers()))),
            baseClause,
            stepClause,
        ]));
    }

    private static Formula SequenceFormula()
    {
        Formula n = F.Id("n");
        return Disp(new Formula.Aligned([
            Seq(F.Id("a"), Colon, Sp, Naturals(), Sp, To, Sp, Integers()),
            Equal(Call("a", D(0)), D(0)),
            Equal(Call("a", D(1)), D(1)),
            Seq(Forall, Sp, Typed(n, Naturals()), Comma, Sp,
                Equal(Call("a", Add(n, D(2))), Call("getD", Call("table", Add(n, D(1))),
                    Add(n, D(2)), D(0)))),
        ]));
    }

    private static Formula InitialResiduesFormula()
    {
        Formula castZero = Call("cast", Call("a", D(0)), Call("ZMod", D(2)));
        Formula castOne = Call("cast", Call("a", D(1)), Call("ZMod", D(2)));
        Formula castTwo = Call("cast", Call("a", D(2)), Call("ZMod", D(2)));
        return Disp(Conjoin(
            Equal(castZero, D(0)),
            Equal(castOne, D(1)),
            Equal(castTwo, D(1))));
    }

    private static Formula RecurrenceFormula()
    {
        Formula n = F.Id("n"), j = F.Id("j");
        Formula a1 = LambdaAt(j, Call("a", Add(j, D(1))));
        Formula a2 = LambdaAt(j, Call("a", Add(j, D(2))));
        Formula rhs = Add(Call("egfPow", a1, D(5), n), Mul(D(3),
            Call("egfMul", Call("egfMul", F.Id("a"), Call("egfPow", a1, D(3))), a2, n)));
        return Disp(Seq(Forall, Sp, Typed(n, Naturals()), Comma, Sp,
            Equal(Call("a", Add(n, D(2))), rhs)));
    }

    private static Formula RecurrencePeriodFormula()
    {
        Formula n = F.Id("n");
        return Disp(Seq(Forall, Sp, Typed(n, Naturals()), Comma, Sp,
            Call("ModEqZ", D(2), Call("a", Add(n, D(3))), Call("a", n))));
    }

    private static Formula ExpDefinesFormula()
    {
        Formula a = F.Id("A"), d = Derivative(a);
        return Disp(Seq(Forall, Sp, Typed(a, PowerSeriesQ()), Comma, Sp,
            Equal(Call("ExpDefines", a), Conjoin(
                Equal(Call("constantCoeff", a), D(0)),
                Equal(d, Call("subst", ExpSeries(), Mul(a, Pow(d, D(3)))))))));
    }

    private static Formula ExpImpliesOdeFormula()
    {
        Formula a = F.Id("A"), d = Derivative(a);
        Formula ode = Equal(Mul(Sub(D(1), Mul(D(3), Mul(a, Pow(d, D(3))))), Derivative(d)),
            Pow(d, D(5)));
        return Disp(Seq(Forall, Sp, Typed(a, PowerSeriesQ()), Comma, Sp,
            Parenthesized(Call("ExpDefines", a)), Sp, Rightarrow, Sp, ode));
    }

    private static Formula EgfSeriesFormula()
    {
        Formula s = F.Id("s"), n = F.Id("n");
        Formula coefficient = new Formula.Fraction(Call("s", n), Factorial(n));
        return Disp(Seq(Forall, Sp, Typed(s, Arrow(Naturals(), Rationals())), Comma, Sp,
            Equal(Call("egfSeries", s), Call("mk", LambdaAt(n, coefficient)))));
    }

    private static Formula FirstDerivativeFormula()
    {
        Formula a = F.Id("A");
        return Disp(Seq(Forall, Sp, Typed(a, PowerSeriesQ()), Comma, Sp,
            Parenthesized(Call("ExpDefines", a)), Sp, Rightarrow, Sp,
            Equal(Call("constantCoeff", Derivative(a)), D(1))));
    }

    private static Formula EgfOdeFormula()
    {
        Formula s = F.Id("s"), n = F.Id("n"), j = F.Id("j");
        Formula s1 = LambdaAt(j, Call("s", Add(j, D(1))));
        Formula s2 = LambdaAt(j, Call("s", Add(j, D(2))));
        Formula rhs = Add(Call("egfPow", s1, D(5), n), Mul(D(3),
            Call("egfMul", Call("egfMul", s, Call("egfPow", s1, D(3))), s2, n)));
        Formula recurrence = Seq(Forall, Sp, Typed(n, Naturals()), Comma, Sp,
            Equal(Call("s", Add(n, D(2))), rhs));
        return Disp(Seq(Forall, Sp, Typed(s, Arrow(Naturals(), Rationals())), Comma, Sp,
            Equal(Call("EgfOde", s), recurrence)));
    }

    private static Formula EgfOdeUniqueFormula()
    {
        Formula s = F.Id("s"), t = F.Id("t");
        Formula hypotheses = Conjoin(
            Equal(Call("s", D(0)), D(0)), Equal(Call("s", D(1)), D(1)),
            Equal(Call("t", D(0)), D(0)), Equal(Call("t", D(1)), D(1)),
            Call("EgfOde", s), Call("EgfOde", t));
        return Disp(Seq(Forall, Sp, Typed(s, Arrow(Naturals(), Rationals())), Comma, Sp,
            Typed(t, Arrow(Naturals(), Rationals())), Comma, Sp,
            Parenthesized(hypotheses), Sp, Rightarrow, Sp, Equal(s, t)));
    }

    private static Formula OeisDefinesFormula()
    {
        Formula s = F.Id("s"), n = F.Id("n");
        Formula castSequence = LambdaAt(n, Call("castQ", Call("s", n)));
        Formula a = Call("egfSeries", castSequence), d = Derivative(a);
        return Disp(Seq(Forall, Sp, Typed(s, Arrow(Naturals(), Integers())), Comma, Sp,
            Equal(Call("OEISDefines", s), Conjoin(
                Equal(Call("constantCoeff", a), D(0)),
                Equal(d, Call("subst", ExpSeries(), Mul(a, Pow(d, D(3)))))))));
    }

    private static Formula OeisWitnessFormula() =>
        Disp(Call("OEISDefines", F.Id("a")));

    private static Formula IdentificationFormula()
    {
        Formula s = F.Id("s");
        return Disp(Seq(Forall, Sp, Typed(s, Arrow(Naturals(), Integers())), Comma, Sp,
            Parenthesized(Call("OEISDefines", s)), Sp, Rightarrow, Sp, Equal(s, F.Id("a"))));
    }

    private static Formula OeisPeriodFormula()
    {
        Formula s = F.Id("s"), n = F.Id("n");
        return Disp(Seq(Forall, Sp, Typed(s, Arrow(Naturals(), Integers())), Comma, Sp,
            Parenthesized(Call("OEISDefines", s)), Sp, Rightarrow, Sp,
            Forall, Sp, Typed(n, Naturals()), Comma, Sp,
            Call("ModEqZ", D(2), Call("s", Add(n, D(3))), Call("s", n))));
    }

    private static Formula ConditionalParityFormula()
    {
        Formula s = F.Id("s"), n = F.Id("n");
        Formula parity = new Formula.Logic(
            Parenthesized(Call("Even", Call("s", n))), FormulaLogicOperator.Iff,
            Parenthesized(new Formula.Relation(D(3), FormulaRelationOperator.Divides, n)));
        return Disp(Seq(Forall, Sp, Typed(s, Arrow(Naturals(), Integers())), Comma, Sp,
            Parenthesized(Call("OEISDefines", s)), Sp, Rightarrow, Sp,
            Forall, Sp, Typed(n, Naturals()), Comma, Sp,
            Parenthesized(new Formula.Relation(D(1), FormulaRelationOperator.LessThanOrEqual, n)),
            Sp, Rightarrow, Sp, parity));
    }

    private static Formula ParityFormula()
    {
        Formula n = F.Id("n");
        Formula parity = new Formula.Logic(
            Parenthesized(Call("Even", Call("a", n))), FormulaLogicOperator.Iff,
            Parenthesized(new Formula.Relation(D(3), FormulaRelationOperator.Divides, n)));
        return Disp(Seq(Forall, Sp, Typed(n, Naturals()), Comma, Sp,
            Parenthesized(new Formula.Relation(D(1), FormulaRelationOperator.LessThanOrEqual, n)),
            Sp, Rightarrow, Sp, parity));
    }

    private static Formula Derivative(Formula value) => Call("DQ", value);
    private static Formula ExpSeries() => Call("expQ");
    private static Formula PowerSeriesQ() => Call("PowerSeries", Rationals());
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Rationals() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Arrow(Formula domain, Formula codomain) => Parenthesized(Seq(domain, Sp, To, Sp, codomain));
    private static Formula Typed(Formula value, Formula type) => Seq(value, Colon, Sp, type);
    private static Formula LambdaAt(Formula variable, Formula body) => Parenthesized(Seq(variable, Sp, Mapsto, Sp, body));
    private static Formula Factorial(Formula value) => Seq(Parenthesized(value), Bang);
    private static Formula Pow(Formula value, Formula exponent) => new Formula.Power(Parenthesized(value), exponent);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula FiniteSum(Formula index, Formula domain, Formula body) =>
        Seq(new Formula.Subscript(F.Sum, Seq(index, Sp, InMacro, Sp, domain)), Sp, Parenthesized(body));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula List(params Formula[] entries)
    {
        var items = new List<Formula> { OpenBracket };
        for (var index = 0; index < entries.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(entries[index]);
        }

        items.Add(CloseBracket);
        return Seq([.. items]);
    }

    private static Formula Conjoin(params Formula[] clauses)
    {
        Formula result = Parenthesized(clauses[^1]);
        for (var index = clauses.Length - 2; index >= 0; index--)
            result = new Formula.Logic(Parenthesized(clauses[index]), FormulaLogicOperator.And, result);
        return result;
    }

    private static Formula PublishedFormula(string name)
    {
        var r = F.Id("R"); var f = F.Id("f"); var g = F.Id("g"); var fp = F.Id("fp");
        var n = F.Id("n"); var k = F.Id("k"); var m = F.Id("m"); var a = F.Id("A");
        Formula All(string x, Formula t, Formula b) => new Formula.BindMany(FormulaQuantifier.ForAll,
            [new(FormulaIdentifier.Create(x), t)], b);
        Formula Imp(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
        Formula Leq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
        Formula PrefixEq(Formula x, Formula y) => All("k", Naturals(), Imp(Leq(k, n), Equal(new Formula.Apply(x, [k]), new Formula.Apply(y, [k]))));
        Formula Generic(Formula b) => Seq(Forall, Sp, Typed(r, F.Id("Type")), Comma, Sp,
            OpenBracket, Call("CommSemiring", r), CloseBracket, Comma, Sp, b);
        return name switch
        {
            "egfOne" => Disp(Generic(All("n", Naturals(), Equal(Call("egfOne", n),
                Parenthesized(Seq(Call("ite", Equal(n, D(0)), D(1), D(0)), Colon, Sp, r)))))),
            "egfPow_congr_at" => Disp(Generic(All("f", Arrow(Naturals(), r), All("fp", Arrow(Naturals(), r),
                All("m", Naturals(), All("n", Naturals(), Imp(PrefixEq(f, fp),
                    Equal(Call("egfPow", f, m, n), Call("egfPow", fp, m, n))))))))),
            "egfSeries_mul" => Disp(All("f", Arrow(Naturals(), Rationals()), All("g", Arrow(Naturals(), Rationals()),
                Equal(Call("egfSeries", Call("egfMul", f, g)), Mul(Call("egfSeries", f), Call("egfSeries", g)))))),
            "egfSeries_pow" => Disp(All("f", Arrow(Naturals(), Rationals()), All("m", Naturals(),
                Equal(Call("egfSeries", Call("egfPow", f, m)), Pow(Call("egfSeries", f), m))))),
            "egfCoeffs" => Disp(All("A", PowerSeriesQ(), All("n", Naturals(),
                Equal(Call("egfCoeffs", a, n), Mul(Parenthesized(Seq(Factorial(n), Colon, Sp, Rationals())), Call("coeff", n, a)))))),
            "egfSeries_egfCoeffs" => Disp(All("A", PowerSeriesQ(), Equal(Call("egfSeries", Call("egfCoeffs", a)), a))),
            _ => throw new System.ArgumentException("Unknown coefficient identity", nameof(name)),
        };
    }
}
