using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization;

internal sealed class JordanCototientRecordLimitInfinityDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Factorization/JordanCototientRecordLimitInfinity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Eventual strict Jordan-cototient records are exactly one and the even naturals.",
        H("Eventual Jordan-Cototient Records"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("jordan-totient-definition"),
                DeclarationHandle.Create(Prefix + "J"),
                H("The real-parameter Jordan totient"),
                StatementSource.FromAuthor(JDefinitionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a real parameter k and a natural number n, J(k,n) is exactly n^k "
                        + "times the product over p in primeFactors(n) of 1-p^(-k). The function "
                        + "val shown in the formula is the coercion from natural numbers to real "
                        + "numbers. This is the definition stated in the OEIS A004277 comment."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("jordan-cototient-definition"),
                DeclarationHandle.Create(Prefix + "CoJ"),
                H("The Jordan cototient"),
                StatementSource.FromAuthor(CoJDefinitionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For real k and natural n, CoJ(k,n) is defined exactly as the real power "
                        + "n^k minus J(k,n), matching the OEIS source comment."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("strict-record-definition"),
                DeclarationHandle.Create(Prefix + "StrictRecord"),
                H("Strict records among positive predecessors"),
                StatementSource.FromAuthor(StrictRecordDefinitionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "StrictRecord(k,n) means that every natural predecessor m with 1 <= m and "
                        + "m < n has strictly smaller Jordan cototient at the same parameter k."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-product-union-bound"),
                DeclarationHandle.Create(Prefix + "one_sub_prod_le_sum"),
                H("A finite-product union bound"),
                StatementSource.FromAuthor(FiniteProductBoundFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a finite subset s of a linearly ordered type and real factors x(i) "
                        + "between zero and one, one minus the product of 1-x(i) is at most "
                        + "the sum of x(i). This bounds finite Euler products and geometric "
                        + "partial products."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("cototient-min-factor-lower-bound"),
                DeclarationHandle.Create(Prefix + "coJ_lower_bound"),
                H("The minimum-prime-factor lower bound"),
                StatementSource.FromAuthor(LowerBoundFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For k > 0 and n > 1, the k-th real power of the natural Euclidean quotient "
                        + "Nat.div(n,minFac(n)) is at most CoJ(k,n). Nat.div is the integer "
                        + "quotient before the displayed real coercion; it is not field division. "
                        + "The proof singles out the minFac(n) term in the finite Euler product."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("cototient-min-factor-upper-bound"),
                DeclarationHandle.Create(Prefix + "coJ_upper_bound"),
                H("The minimum-prime-factor upper bound"),
                StatementSource.FromAuthor(UpperBoundFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For k > 0 and n > 1, CoJ(k,n) is at most the real coercion of the number "
                        + "of distinct prime factors times the k-th power of "
                        + "Nat.div(n,minFac(n)). Nat.div again denotes natural Euclidean division. "
                        + "A finite-product union bound compares every reciprocal prime scale "
                        + "with the minimum-prime-factor scale."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("prime-cototient-value"),
                DeclarationHandle.Create(Prefix + "coJ_prime"),
                H("Prime inputs have cototient one"),
                StatementSource.FromAuthor(PrimeValueFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every natural prime p has CoJ(k,p)=1 for every real k. This "
                        + "evaluation is consumed by the two-versus-three tie in "
                        + "not_strictRecord_three."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("one-cototient-value"),
                DeclarationHandle.Create(Prefix + "coJ_one"),
                H("The cototient of one vanishes"),
                StatementSource.FromAuthor(OneValueFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every real k, CoJ(k,1)=0 because primeFactors(1) is empty. This "
                        + "evaluation supplies the m=1 predecessor case in the even "
                        + "record theorem."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("even-input-eventual-record"),
                DeclarationHandle.Create(Prefix + "eventual_strictRecord_of_even"),
                H("Every positive even input is eventually a strict record"),
                StatementSource.FromAuthor(EvenRecordFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If n is positive and even, there is a real threshold K after which n is "
                        + "a strict record. The proof combines the two cototient bounds with the "
                        + "strict base gap m/minFac(m) <= m/2 < n/2 and real exponential "
                        + "domination. Each slash in this prose is real division after coercion, "
                        + "whereas the Lean bounds themselves use the named Nat.div quotient."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("odd-input-eventual-loss"),
                DeclarationHandle.Create(Prefix + "eventual_loses_to_predecessor_of_odd"),
                H("Odd inputs at least five eventually lose to their predecessor"),
                StatementSource.FromAuthor(OddLossFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If n is odd and at least five, a real threshold K makes CoJ(k,n) smaller "
                        + "than CoJ(k,Nat.sub(n,1)) for every k > K. Nat.sub is truncated natural "
                        + "subtraction. The proof uses n/minFac(n) <= n/3 < (n-1)/2 and the same "
                        + "real exponential-domination lemma."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("three-is-never-a-strict-record"),
                DeclarationHandle.Create(Prefix + "not_strictRecord_three"),
                H("Three is never a strict record"),
                StatementSource.FromAuthor(ThreeNotRecordFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every real k, three is not a strict record: the preceding prime-value "
                        + "lemma gives CoJ(k,2)=CoJ(k,3)=1, so the required strict predecessor "
                        + "inequality is impossible."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("a004277-eventual-record-characterization"),
                DeclarationHandle.Create(Prefix + "a004277_eventual_record_iff"),
                H("The eventual record set is one together with the even naturals"),
                StatementSource.FromAuthor(MainFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural n >= 1, there exists a real threshold K after which n "
                            + "is always a strict Jordan-cototient record exactly when n=1 or n "
                            + "is even. The threshold is chosen separately for each n; no uniform "
                            + "threshold over all even inputs is asserted.")),
                    Paragraph(Text(
                        "The forward direction excludes three by the prime tie and every odd "
                            + "n >= 5 by its eventual loss to Nat.sub(n,1). The reverse direction "
                            + "is vacuous at one and uses the even-input theorem otherwise. "
                            + "Thus the two-sided min-factor estimates remain in the derivation "
                            + "to the final characterization."))),
                DescribeRole.Theorem))));

    private static Formula FiniteProductBoundFormula()
    {
        Formula i = F.Id("i"), s = F.Id("s"), x = F.Id("x");
        Formula xi = new Formula.Apply(x, [i]);
        Formula index = new Formula.Relation(i, FormulaRelationOperator.MemberOf, s);
        Formula allFactors = ForAllMany([Bound("i", F.Id("I"))],
            Implies(index, new Formula.Logic(
                LessThanOrEqual(D(0), xi), FormulaLogicOperator.And,
                LessThanOrEqual(xi, D(1)))));
        Formula product = Seq(new Formula.Subscript(Prod, index), Sp,
            Parenthesized(Subtract(D(1), xi)));
        Formula sum = Seq(new Formula.Subscript(Sum, index), Sp, xi);
        return Disp(ForAllMany([Bound("I", F.Id("Type"))], Seq(
            OpenBracket, Call("LinearOrder", F.Id("I")), CloseBracket, Sp,
            ForAllMany(
                [Bound("s", Call("Finset", F.Id("I"))),
                    Bound("x", new Formula.TypeArrow(F.Id("I"), Reals()))],
                Implies(allFactors, LessThanOrEqual(Subtract(D(1), product), sum))))));
    }

    private static Formula JDefinitionFormula()
    {
        Formula k = F.Id("k"), n = F.Id("n"), p = F.Id("p");
        Formula factor = Subtract(D(1), Power(Val(p), Negate(k)));
        Formula value = Multiply(Power(Val(n), k), ProductOverPrimeFactors(p, n, factor));
        return Disp(ForAllMany(
            [Bound("k", Reals()), Bound("n", Naturals())],
            Equal(Call("J", k, n), value)));
    }

    private static Formula CoJDefinitionFormula()
    {
        Formula k = F.Id("k"), n = F.Id("n");
        return Disp(ForAllMany(
            [Bound("k", Reals()), Bound("n", Naturals())],
            Equal(Call("CoJ", k, n), Subtract(Power(Val(n), k), Call("J", k, n)))));
    }

    private static Formula StrictRecordDefinitionFormula()
    {
        Formula k = F.Id("k"), n = F.Id("n"), m = F.Id("m");
        Formula predecessors = ForAllMany(
            [Bound("m", Naturals())],
            Implies(
                LessThanOrEqual(D(1), m),
                Implies(LessThan(m, n), LessThan(Call("CoJ", k, m), Call("CoJ", k, n)))));
        return Disp(ForAllMany(
            [Bound("k", Reals()), Bound("n", Naturals())],
            Iff(Call("StrictRecord", k, n), predecessors)));
    }

    private static Formula LowerBoundFormula()
    {
        Formula k = F.Id("k"), n = F.Id("n");
        Formula conclusion = LessThanOrEqual(
            Power(Val(NatDiv(n, MinFac(n))), k), Call("CoJ", k, n));
        return Disp(ForAllMany(
            [Bound("k", Reals()), Bound("n", Naturals())],
            Implies(LessThan(D(0), k), Implies(LessThan(D(1), n), conclusion))));
    }

    private static Formula UpperBoundFormula()
    {
        Formula k = F.Id("k"), n = F.Id("n");
        Formula coefficient = Val(Call("card", PrimeFactors(n)));
        Formula upper = Multiply(coefficient, Power(Val(NatDiv(n, MinFac(n))), k));
        return Disp(ForAllMany(
            [Bound("k", Reals()), Bound("n", Naturals())],
            Implies(
                LessThan(D(0), k),
                Implies(LessThan(D(1), n), LessThanOrEqual(Call("CoJ", k, n), upper)))));
    }

    private static Formula PrimeValueFormula()
    {
        Formula p = F.Id("p"), k = F.Id("k");
        return Disp(ForAllMany(
            [Bound("p", Naturals()), Bound("k", Reals())],
            Implies(Call("Prime", p), Equal(Call("CoJ", k, p), D(1)))));
    }

    private static Formula OneValueFormula()
    {
        Formula k = F.Id("k");
        return Disp(ForAllMany(
            [Bound("k", Reals())], Equal(Call("CoJ", k, D(1)), D(0))));
    }

    private static Formula EvenRecordFormula()
    {
        Formula n = F.Id("n");
        return Disp(ForAllMany(
            [Bound("n", Naturals())],
            Implies(
                LessThanOrEqual(D(1), n),
                Implies(Call("Even", n), EventualStrictRecord(n)))));
    }

    private static Formula OddLossFormula()
    {
        Formula n = F.Id("n"), k = F.Id("k"), threshold = F.Id("K");
        Formula eventualLoss = ExistsMany(
            [Bound("K", Reals())],
            ForAllMany(
                [Bound("k", Reals())],
                Implies(
                    GreaterThan(k, threshold),
                    LessThan(Call("CoJ", k, n), Call("CoJ", k, NatSub(n, D(1)))))));
        return Disp(ForAllMany(
            [Bound("n", Naturals())],
            Implies(
                LessThanOrEqual(D(5), n),
                Implies(new Formula.Not(Call("Even", n)), eventualLoss))));
    }

    private static Formula ThreeNotRecordFormula()
    {
        Formula k = F.Id("k");
        return Disp(ForAllMany(
            [Bound("k", Reals())], new Formula.Not(Call("StrictRecord", k, D(3)))));
    }

    private static Formula MainFormula()
    {
        Formula n = F.Id("n");
        Formula classification = Or(Equal(n, D(1)), Call("Even", n));
        return Disp(ForAllMany(
            [Bound("n", Naturals())],
            Implies(
                LessThanOrEqual(D(1), n),
                Iff(Parenthesized(EventualStrictRecord(n)), Parenthesized(classification)))));
    }

    private static Formula EventualStrictRecord(Formula n)
    {
        Formula k = F.Id("k"), threshold = F.Id("K");
        return ExistsMany(
            [Bound("K", Reals())],
            ForAllMany(
                [Bound("k", Reals())],
                Implies(GreaterThan(k, threshold), Call("StrictRecord", k, n))));
    }

    private static Formula ProductOverPrimeFactors(Formula prime, Formula n, Formula body)
    {
        Formula index = new Formula.Relation(
            prime, FormulaRelationOperator.MemberOf, PrimeFactors(n));
        return Seq(new Formula.Subscript(Prod, index), Sp, Parenthesized(body));
    }

    private static Formula PrimeFactors(Formula n) => Call("primeFactors", n);

    private static Formula MinFac(Formula n) => Call("minFac", n);

    private static Formula NatDiv(Formula left, Formula right) =>
        Apply(Qualified("Nat", "div"), left, right);

    private static Formula NatSub(Formula left, Formula right) =>
        Apply(Qualified("Nat", "sub"), left, right);

    private static Formula Val(Formula value) => Call("val", value);

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);

    private static Formula Negate(Formula value) => Seq(Minus, value);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Qualified(params string[] names)
    {
        Formula result = F.Id(names[0]);
        foreach (var name in names[1..])
            result = Seq(result, Dot, F.Id(name));
        return Seq(Operatorname, Grp(result));
    }

    private static Formula.BoundVariable Bound(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);

    private static Formula ForAllMany(
        Formula.BoundVariable[] variables,
        Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula ExistsMany(
        Formula.BoundVariable[] variables,
        Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LessThan(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessThanOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula GreaterThan(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.GreaterThan, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Or, right);
}
