using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization;

internal sealed class PrimeExponentRecordLimitOneDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Factorization/PrimeExponentRecordLimitOne.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every fixed positive integer, strict prime-exponent record membership near one "
            + "from the left is exactly membership in A029744 with the term three removed.",
        H("Prime-Exponent Record Limit at One"),
        Blocks(
            Entry("f", "prime-exponent-score", "The prime-exponent score",
                ScoreDefinition(), DescribeRole.Definition,
                "For real x and natural n, f(x,n) is the finite sum over the distinct prime "
                    + "divisors p of n of the real x-th power of the natural exponent of p in n. "
                    + "The displayed real coercion is part of the definition. OEIS A384669 "
                    + "(Switkay, 2025-06-06) supplies this score definition.",
                AssessedProvenance.FromRepo()),
            Entry("StrictRecord", "prime-exponent-strict-record", "Strict record membership",
                StrictRecordDefinition(), DescribeRole.Definition,
                "StrictRecord(x,n) requires n to be positive and f(x,n) to exceed f(x,m) for "
                    + "every positive natural m strictly below n. OEIS A384669 (Switkay, "
                    + "2025-06-06) supplies this strict-record definition.",
                AssessedProvenance.FromRepo()),
            Entry("f_one", "prime-exponent-score-at-one", "The score at one",
                ScoreAtOneFormula(), DescribeRole.Theorem,
                "At x=1 the score is Mathlib's cardFactors, the number of prime factors counted "
                    + "with multiplicity, by the factorization sum identity.",
                AssessedProvenance.FromRepo()),
            Entry("odd_part_lower", "odd-part-prime-product-lower-bound",
                "The odd-part prime-product bound", OddPartLowerFormula(), DescribeRole.Theorem,
                "For a nonzero odd natural m, three raised to the length of its prime-factor "
                    + "list is at most m. Each listed prime is at least three, and the list "
                    + "product is m. Mathlib's cardFactors_apply identifies this length with "
                    + "the prime-factor count with multiplicity. The estimate supplies both "
                    + "the prime-product gap here and the odd-weight bound in JLTConjecture.",
                AssessedProvenance.FromRepo()),
            Entry("gap_lemma", "prime-exponent-gap", "The prime-product gap",
                GapFormula(), DescribeRole.Theorem,
                "If nonzero n is neither a power of two nor three times a power of two, then the "
                    + "power 2^(cardFactors(n)+1) is strictly smaller than n. Writing n as a power "
                    + "of two times an odd part, one odd prime at least five gives ratio at least "
                    + "5/2, while at least two factors three give ratio at least 9/4. This gap "
                    + "lemma is repository-derived.", AssessedProvenance.FromRepo()),
            Entry("eventually_not_record_of_gap", "prime-exponent-eventual-exclusion",
                "Gap numbers are eventually excluded", EventuallyNotRecordFormula(),
                DescribeRole.Theorem,
                "The smaller power of two supplied by the gap lemma has score cardFactors(n)+1 "
                    + "at x=1, strictly above the score of n. Continuity of the two finite score "
                    + "sums transports this defeat to a left neighborhood of one.",
                AssessedProvenance.FromRepo()),
            Entry("eventually_two_pow_record", "prime-exponent-powers-two-record",
                "Powers of two are eventual records", EventuallyTwoPowerFormula(),
                DescribeRole.Theorem,
                "Every positive predecessor of 2^k has fewer than k prime factors counted with "
                    + "multiplicity. The finitely many strict inequalities at x=1 therefore "
                    + "persist simultaneously on a left neighborhood of one; k=0 is vacuous.",
                AssessedProvenance.FromRepo()),
            Entry("strict_subadditive_rpow", "strict-subadditivity-real-power",
                "Strict subadditivity below one", StrictSubadditiveFormula(),
                DescribeRole.Theorem,
                "For positive natural k and real 0<x<1, strict concavity gives "
                    + "(k+1)^x < k^x+1. The proof obtains the strict inequality via Mathlib's "
                    + "Real.strictConcaveOn_rpow; this supporting bridge is repository-derived, "
                    + "not a newly asserted classical result.", AssessedProvenance.FromRepo()),
            Entry("not_record_three", "prime-exponent-three-not-record",
                "Three is never a positive-exponent record", NotRecordThreeFormula(),
                DescribeRole.Theorem,
                "For every positive real exponent, two and three both have score one. Since two "
                    + "is a smaller positive integer, three cannot be a strict record.",
                AssessedProvenance.FromRepo()),
            Entry("eventually_three_two_record", "prime-exponent-three-two-record",
                "Three times a positive power of two is an eventual record",
                EventuallyThreeTwoFormula(), DescribeRole.Theorem,
                "Below 3*2^k, any number with fewer than k+1 prime factors loses already at one. "
                    + "The only smaller number with exactly k+1 factors is 2^(k+1), and strict "
                    + "subadditivity breaks that tie in favor of 3*2^k for 0<x<1.",
                AssessedProvenance.FromRepo()),
            Entry("Candidate", "prime-exponent-endpoint-candidates",
                "The endpoint candidate family", CandidateDefinition(), DescribeRole.Definition,
                "Candidate(n) means that n is a power of two, or is three times 2^k for a "
                    + "positive natural k. Thus the definition is exactly A029744 with its term "
                    + "three omitted. OEIS A029744 supplies the powers-of-two and "
                    + "three-times-powers-of-two family.", AssessedProvenance.FromRepo()),
            Entry("a384669_endpoint_limit_one", "a384669-endpoint-limit-one",
                "The A384669 endpoint at one", EndpointFormula(), DescribeRole.Theorem,
                "For every fixed positive n there is a real 0<delta<1 such that, whenever "
                    + "1-delta<x<1, n is a strict record exactly when it is a power of two or "
                    + "three times a positive power of two. The power-of-two, three-times-power, "
                    + "three, and gap cases exhaust the positive naturals. This is limited to the "
                    + "per-n eventual formulation: no uniform delta and no sequence-level limit "
                    + "are claimed. OEIS A384669 supplies the sequence-level conjectural target; "
                    + "the per-n quantifiers proved here are repository-derived.",
                AssessedProvenance.FromRepo()))));

    private static DocumentBlock.Describe Entry(string declaration, string id, string title,
        Formula formula, DescribeRole role, string text, AssessedProvenance provenance) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(text))), role);

    private static Formula ScoreDefinition()
    {
        Formula x = F.Id("x"), n = F.Id("n"), p = F.Id("p");
        Formula index = Seq(p, Sp, InMacro, Sp, Call("primeFactors", n));
        Formula summand = Power(Call("real", Call("factorization", n, p)), x);
        Formula sum = Seq(new Formula.Subscript(Sum, index), Sp, summand);
        return Disp(ForAll([Bound("x", Reals()), Bound("n", Naturals())],
            Equal(Call("f", x, n), sum)));
    }

    private static Formula StrictRecordDefinition()
    {
        Formula x = F.Id("x"), n = F.Id("n"), m = F.Id("m");
        Formula predecessor = ForAll([Bound("m", Naturals())],
            Implies(Le(D(1), m), Implies(Lt(m, n), Lt(Call("f", x, m), Call("f", x, n)))));
        return Disp(ForAll([Bound("x", Reals()), Bound("n", Naturals())],
            Iff(Call("StrictRecord", x, n), And(Le(D(1), n), predecessor))));
    }

    private static Formula ScoreAtOneFormula()
    {
        Formula n = F.Id("n");
        return Disp(ForAll([Bound("n", Naturals())],
            Equal(Call("f", D(1), n), Call("real", Call("cardFactors", n)))));
    }

    private static Formula OddPartLowerFormula()
    {
        Formula m = F.Id("m");
        Formula hypotheses = And(NotEqual(m, D(0)), Call("Odd", m));
        Formula exponent = Call("length", Call("primeFactorsList", m));
        return Disp(ForAll([Bound("m", Naturals())],
            Implies(hypotheses, Le(Power(D(3), exponent), m))));
    }

    private static Formula GapFormula()
    {
        Formula n = F.Id("n");
        Formula hypotheses = And(NotEqual(n, D(0)), NotPowerOfTwo(n), NotThreeTwoPower(n));
        Formula bound = Lt(Power(D(2), Add(Call("cardFactors", n), D(1))), n);
        return Disp(ForAll([Bound("n", Naturals())], Implies(hypotheses, bound)));
    }

    private static Formula EventuallyNotRecordFormula()
    {
        Formula n = F.Id("n"), x = F.Id("x"), delta = F.Id("delta");
        Formula hypotheses = And(NotEqual(n, D(0)), NotPowerOfTwo(n), NotThreeTwoPower(n));
        Formula conclusion = Some([Bound("delta", Reals())], And(Lt(D(0), delta), Lt(delta, D(1)),
            ForAll([Bound("x", Reals())], Implies(Lt(Subtract(D(1), delta), x),
                Implies(Lt(x, D(1)), new Formula.Not(Call("StrictRecord", x, n)))))));
        return Disp(ForAll([Bound("n", Naturals())], Implies(hypotheses, conclusion)));
    }

    private static Formula EventuallyTwoPowerFormula()
    {
        Formula k = F.Id("k"), x = F.Id("x"), delta = F.Id("delta");
        Formula conclusion = Some([Bound("delta", Reals())], And(Lt(D(0), delta), Lt(delta, D(1)),
            ForAll([Bound("x", Reals())], Implies(Lt(Subtract(D(1), delta), x),
                Implies(Lt(x, D(1)), Call("StrictRecord", x, Power(D(2), k)))))));
        return Disp(ForAll([Bound("k", Naturals())], conclusion));
    }

    private static Formula StrictSubadditiveFormula()
    {
        Formula k = F.Id("k"), x = F.Id("x");
        Formula hypotheses = And(Lt(D(0), k), Lt(D(0), x), Lt(x, D(1)));
        Formula lhs = Power(Call("real", Add(k, D(1))), x);
        Formula rhs = Add(Power(Call("real", k), x), D(1));
        return Disp(ForAll([Bound("k", Naturals()), Bound("x", Reals())],
            Implies(hypotheses, Lt(lhs, rhs))));
    }

    private static Formula NotRecordThreeFormula()
    {
        Formula x = F.Id("x");
        return Disp(ForAll([Bound("x", Reals())], Implies(Lt(D(0), x),
            new Formula.Not(Call("StrictRecord", x, D(3))))));
    }

    private static Formula EventuallyThreeTwoFormula()
    {
        Formula k = F.Id("k"), x = F.Id("x"), delta = F.Id("delta");
        Formula n = Multiply(D(3), Power(D(2), k));
        Formula conclusion = Some([Bound("delta", Reals())], And(Lt(D(0), delta), Lt(delta, D(1)),
            ForAll([Bound("x", Reals())], Implies(Lt(Subtract(D(1), delta), x),
                Implies(Lt(x, D(1)), Call("StrictRecord", x, n))))));
        return Disp(ForAll([Bound("k", Naturals())],
            Implies(Lt(D(0), k), conclusion)));
    }

    private static Formula CandidateDefinition()
    {
        Formula n = F.Id("n");
        return Disp(ForAll([Bound("n", Naturals())],
            Iff(Call("Candidate", n), CandidateFamily(n))));
    }

    private static Formula EndpointFormula()
    {
        Formula n = F.Id("n"), x = F.Id("x"), delta = F.Id("delta");
        Formula equivalence = Iff(Call("StrictRecord", x, n), CandidateFamily(n));
        Formula conclusion = Some([Bound("delta", Reals())], And(Lt(D(0), delta), Lt(delta, D(1)),
            ForAll([Bound("x", Reals())], Implies(Lt(Subtract(D(1), delta), x),
                Implies(Lt(x, D(1)), equivalence)))));
        return Disp(ForAll([Bound("n", Naturals())],
            Implies(Le(D(1), n), conclusion)));
    }

    private static Formula CandidateFamily(Formula n)
    {
        Formula k = F.Id("k");
        Formula power = Some([Bound("k", Naturals())], Equal(n, Power(D(2), k)));
        Formula threePower = Some([Bound("k", Naturals())],
            And(Le(D(1), k), Equal(n, Multiply(D(3), Power(D(2), k)))));
        return Parenthesized(Or(power, threePower));
    }

    private static Formula NotPowerOfTwo(Formula n)
    {
        Formula k = F.Id("k");
        return ForAll([Bound("k", Naturals())], NotEqual(n, Power(D(2), k)));
    }

    private static Formula NotThreeTwoPower(Formula n)
    {
        Formula k = F.Id("k");
        return ForAll([Bound("k", Naturals())],
            NotEqual(n, Multiply(D(3), Power(D(2), k))));
    }

    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Some(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Or, Parenthesized(right));

    private static Formula And(params Formula[] clauses)
    {
        Formula result = Parenthesized(clauses[^1]);
        for (int index = clauses.Length - 2; index >= 0; index--)
            result = new Formula.Logic(
                Parenthesized(clauses[index]), FormulaLogicOperator.And, result);
        return result;
    }

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
}
