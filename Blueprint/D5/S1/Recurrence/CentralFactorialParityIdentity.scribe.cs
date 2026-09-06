using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class CentralFactorialParityIdentityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A universal half-shift factorization proves two central-factorial coefficient identities.",
        H("Central-Factorial Parity Identities"),
        Blocks(
            Paragraph(Text(
                "The two final statements match the conjectured formulas (4.27) and (4.41) "
                + "in S. Yakubovich, On the generalized Dirichlet beta and Riemann zeta functions "
                + "and Ramanujan-type formulae for beta and zeta values, arXiv:2405.03294, section 4. "
                + "The proofs below are derived here from polynomial products and coefficient extraction. "
                + "This citation identifies the questions being answered, not an external proof.")),
            Paragraph(Text(
                "All polynomial equalities are in Q[X]. C denotes Polynomial.C, comp is polynomial "
                + "composition, and coeff(P,K) is the coefficient of X^K. The notation t(N,K) denotes "
                + "centralFactorial N K; A_n, C_n and F_n denote A n, Cpoly n and F n. "
                + "The map rat is the natural-number cast into Q. The operator div is natural-number "
                + "division, and mod is its remainder. Subtraction between natural-number indices is "
                + "truncated at zero; subtraction involving rat is rational subtraction. "
                + "Icc(a,b) is the inclusive natural interval, empty when b<a; range(a) is 0 through a-1. "
                + "The operator choose is Nat.choose, with value zero when its lower index exceeds its upper index.")),
            Describe.Lean(
                DescribeId.Create("central-factorial-definition"),
                DeclarationHandle.Create("D5/S1/Recurrence/CentralFactorialParityIdentity.centralFactorial"),
                H("Signed Rational Central-Factorial Coefficients"),
                StatementSource.FromAuthor(CentralFactorialFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "These are the defining even and odd products, including all zero coefficients. "
                    + "The private squareProduct abbreviation has been expanded in this display. "
                    + "No absolute values or odd-row rescaling enter the definition. "
                    + "The paper's first-kind even and odd product conventions are (1.22) and (1.24)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("central-factorial-integer-root-polynomial"),
                DeclarationHandle.Create("D5/S1/Recurrence/CentralFactorialParityIdentity.A"),
                H("Integer-Root Odd Polynomial"),
                StatementSource.FromAuthor(AFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The leading X is outside the product, exactly as in the definition."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("central-factorial-half-integer-polynomial"),
                DeclarationHandle.Create("D5/S1/Recurrence/CentralFactorialParityIdentity.Cpoly"),
                H("Half-Integer-Root Even Polynomial"),
                StatementSource.FromAuthor(CpolyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The factors use j minus one half, with j starting at one."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("central-factorial-evenness"),
                DeclarationHandle.Create("D5/S1/Recurrence/CentralFactorialParityIdentity.Cpoly_even"),
                H("Evenness of the Half-Integer-Root Product"),
                StatementSource.FromAuthor(CpolyEvenFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each quadratic factor is unchanged by substituting zero minus X."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("central-factorial-scaled-shift"),
                DeclarationHandle.Create("D5/S1/Recurrence/CentralFactorialParityIdentity.F"),
                H("Scaled Shift Polynomial"),
                StatementSource.FromAuthor(FFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Multiplication by C(1/2) scales the polynomial after composition."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("central-factorial-half-shift"),
                DeclarationHandle.Create("D5/S1/Recurrence/CentralFactorialParityIdentity.half_shift"),
                H("Universal Half-Shift Factorization"),
                StatementSource.FromAuthor(HalfShiftFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Induction pairs each new integer-root quadratic with the preceding linear factor. "
                    + "This produces the half-integer-root product uniformly in n."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("central-factorial-scaled-factorization"),
                DeclarationHandle.Create("D5/S1/Recurrence/CentralFactorialParityIdentity.F_factorization"),
                H("Scaled Linear Times Even Factorization"),
                StatementSource.FromAuthor(FactorizationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Compose the half-shift identity with X/2 and multiply by one half. "
                    + "The resulting constant polynomial factor is C(1/4)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("central-factorial-adjacent-coefficients"),
                DeclarationHandle.Create("D5/S1/Recurrence/CentralFactorialParityIdentity.adjacent_coefficients"),
                H("Adjacent Coefficient Relation"),
                StatementSource.FromAuthor(AdjacentFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The second factor is even, so each adjacent even and odd coefficient pair "
                    + "has the displayed ratio, including coefficients beyond the degree."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("central-factorial-identity-427"),
                DeclarationHandle.Create("D5/S1/Recurrence/CentralFactorialParityIdentity.identity_427"),
                H("Parity Identity"),
                StatementSource.FromAuthor(Identity427Formula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Compare the odd coefficients of F in its defining expansion and its factorization. "
                    + "The statement covers all positive n and k, without a k<=n hypothesis. "
                    + "The notation (1/4)^k equals 4 raised to the integer exponent -k."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("central-factorial-adjacent-binomial"),
                DeclarationHandle.Create("D5/S1/Recurrence/CentralFactorialParityIdentity.choose_adjacent"),
                H("Adjacent Binomial Relation"),
                StatementSource.FromAuthor(ChooseAdjacentFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For positive j and l, specialize p=2j-1 and d=l-1 to obtain the named "
                    + "2j and l relation. The proof applies Mathlib's Nat.add_one_mul_choose_eq, "
                    + "rewrites with Nat.choose_succ_succ', and casts the equality into Q."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("central-factorial-weighted-reduction"),
                DeclarationHandle.Create("D5/S1/Recurrence/CentralFactorialParityIdentity.weighted_sum_reduction"),
                H("Weighted Sum Reduction"),
                StatementSource.FromAuthor(WeightedSumReductionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The upper coefficient index is l=2(n-m-1)+1. The reflected coefficient "
                    + "expansion and adjacent-binomial relation give the displayed scalar multiple."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("central-factorial-identity-441"),
                DeclarationHandle.Create("D5/S1/Recurrence/CentralFactorialParityIdentity.identity_441"),
                H("Weighted Vanishing Sum"),
                StatementSource.FromAuthor(Identity441Formula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Reflect the coefficient expansion, use the parity identity for its odd part, "
                    + "and apply the adjacent-binomial relation. The weighted sum is a scalar multiple "
                    + "of the vanishing adjacent-coefficient difference. The parity identity is a "
                    + "prerequisite on the live proof path, in consumer-to-prerequisite direction."))),
                DescribeRole.Theorem))));

    private static Formula CentralFactorialFormula()
    {
        Formula n = F.Id("N"), k = F.Id("K"), j = F.Id("j");
        Formula domain = Call("range", Call("div", n, D(2)));
        Formula evenProduct = Product(j, domain, Difference(Power(X(), D(2)),
            Constant(Power(Rat(j), D(2)))));
        Formula oddProduct = Product(j, domain, Difference(Power(X(), D(2)),
            Constant(Power(Parenthesized(Add(Rat(j), Half())), D(2)))));
        Formula remainder = new Formula.Modulo(n, D(2));
        return Disp(new Formula.Aligned([
            Bound(n, k),
            Seq(Call("t", n, k), Colon, Sp, Rationals(), Comma),
            Seq(Parenthesized(Equal(remainder, D(0))), Sp, Rightarrow, Sp,
                Equal(Call("t", n, k), Coeff(evenProduct, k)), Comma),
            Seq(Parenthesized(new Formula.Relation(remainder,
                FormulaRelationOperator.NotEqual, D(0))), Sp, Rightarrow, Sp,
                Equal(Call("t", n, k), Coeff(Multiply(X(), oddProduct), k)), Dot),
        ]));
    }

    private static Formula AFormula()
    {
        Formula n = F.Id("n"), j = F.Id("j");
        return Disp(new Formula.Aligned([
            Bound(n),
            Equal(Indexed("A", n), Multiply(X(), Product(j,
                Call("Icc", D(1), Difference(n, D(1))),
                Difference(Power(X(), D(2)), Constant(Power(Rat(j), D(2))))))),
        ]));
    }

    private static Formula CpolyFormula()
    {
        Formula n = F.Id("n"), j = F.Id("j");
        return Disp(new Formula.Aligned([
            Bound(n),
            Equal(Indexed("C", n), Product(j, Call("Icc", D(1), Difference(n, D(1))),
                Difference(Power(X(), D(2)),
                    Constant(Power(Parenthesized(Difference(Rat(j), Half())), D(2)))))),
        ]));
    }

    private static Formula FFormula()
    {
        Formula n = F.Id("n");
        return Disp(new Formula.Aligned([
            Bound(n),
            Equal(Indexed("F", n), Multiply(Constant(Half()),
                Compose(Indexed("A", n), Multiply(Constant(Half()), Parenthesized(Add(D(1), X())))))),
        ]));
    }

    private static Formula CpolyEvenFormula()
    {
        Formula n = F.Id("n");
        return Disp(new Formula.Aligned([
            Bound(n),
            Equal(Compose(Indexed("C", n), Difference(D(0), X())), Indexed("C", n)),
        ]));
    }

    private static Formula ChooseAdjacentFormula()
    {
        Formula p = F.Id("p"), d = F.Id("d");
        return Disp(new Formula.Aligned([
            Bound(p, d),
            Equal(Multiply(Rat(Add(p, D(1))), Rat(Call("choose", p, d))),
                Multiply(Parenthesized(Add(Rat(Call("choose", p, d)),
                    Rat(Call("choose", p, Add(d, D(1)))))), Rat(Add(d, D(1))))),
        ]));
    }

    private static Formula HalfShiftFormula()
    {
        Formula n = F.Id("n");
        return Disp(new Formula.Aligned([
            Bound(n), Positive(n),
            Equal(Compose(Indexed("A", n), Add(X(), Constant(Half()))),
                Multiply(Parenthesized(Add(X(), Constant(Difference(Rat(n), Half())))), Indexed("C", n))),
        ]));
    }

    private static Formula FactorizationFormula()
    {
        Formula n = F.Id("n");
        return Disp(new Formula.Aligned([
            Bound(n), Positive(n),
            Equal(Indexed("F", n), Multiply(Multiply(Constant(Quarter()),
                Parenthesized(Add(X(), Constant(Difference(Twice(Rat(n)), D(1)))))),
                Compose(Indexed("C", n), Multiply(Constant(Half()), X())))),
        ]));
    }

    private static Formula AdjacentFormula()
    {
        Formula n = F.Id("n"), r = F.Id("r");
        return Disp(new Formula.Aligned([
            Bound(n, r), Positive(n),
            Equal(Coeff(Indexed("F", n), Twice(r)),
                Multiply(Parenthesized(Difference(Twice(Rat(n)), D(1))),
                    Coeff(Indexed("F", n), Add(Twice(r), D(1))))),
        ]));
    }

    private static Formula Identity427Formula()
    {
        Formula n = F.Id("n"), k = F.Id("k"), q = F.Id("q");
        Formula summand = Multiply(Multiply(Power(Parenthesized(Quarter()), q),
            Rat(Call("choose", Difference(Twice(q), D(1)), Difference(Twice(k), D(1))))),
            Call("t", Twice(n), Twice(q)));
        return Disp(new Formula.Aligned([
            Bound(n, k), Positive(n), Positive(k),
            Equal(Multiply(Power(Parenthesized(Quarter()), k),
                Call("t", Difference(Twice(n), D(1)), Difference(Twice(k), D(1)))),
                Summation(q, Call("Icc", k, n), summand)),
        ]));
    }

    private static Formula Identity441Formula()
    {
        Formula n = F.Id("n"), m = F.Id("m"), k = F.Id("k");
        Formula index = Twice(Parenthesized(Difference(n, k)));
        Formula lower = Twice(Parenthesized(Difference(Difference(n, m), D(1))));
        Formula weight = Add(Multiply(Twice(n), Parenthesized(Difference(m, k))), k);
        Formula summand = Multiply(Multiply(Multiply(Power(D(4), k), Call("t", Twice(n), index)),
            Rat(Call("choose", Difference(index, D(1)), lower))), Rat(weight));
        return Disp(new Formula.Aligned([
            Bound(n, m), Positive(n),
            Seq(Parenthesized(new Formula.Relation(m, FormulaRelationOperator.LessThanOrEqual,
                Difference(n, D(1)))), Sp, Rightarrow),
            Equal(Summation(k, Call("range", Add(m, D(1))), summand), D(0)),
        ]));
    }

    private static Formula WeightedSumReductionFormula()
    {
        Formula n = F.Id("n"), m = F.Id("m"), k = F.Id("k");
        Formula index = Twice(Parenthesized(Difference(n, k)));
        Formula lower = Twice(Parenthesized(Difference(Difference(n, m), D(1))));
        Formula upper = Add(lower, D(1));
        Formula weight = Add(Multiply(Twice(n), Parenthesized(Difference(m, k))), k);
        Formula summand = Multiply(Multiply(Multiply(Power(D(4), k), Call("t", Twice(n), index)),
            Rat(Call("choose", Difference(index, D(1)), lower))), Rat(weight));
        return Disp(new Formula.Aligned([
            Bound(n, m), Positive(n),
            Seq(Parenthesized(new Formula.Relation(m, FormulaRelationOperator.LessThanOrEqual,
                Difference(n, D(1)))), Sp, Rightarrow),
            Equal(Summation(k, Call("range", Add(m, D(1))), summand),
                Multiply(new Formula.Fraction(Multiply(Power(D(4), n), Rat(upper)), D(2)),
                    Parenthesized(Difference(Multiply(Parenthesized(Difference(Twice(Rat(n)), D(1))),
                        Coeff(Indexed("F", n), upper)), Coeff(Indexed("F", n), lower))))),
        ]));
    }

    private static Formula Bound(params Formula[] variables) =>
        Seq(Forall, Sp, Joined(variables, Comma), Sp, InMacro, Sp, Naturals(), Comma);
    private static Formula Positive(Formula n) =>
        Seq(Parenthesized(new Formula.Relation(D(1), FormulaRelationOperator.LessThanOrEqual, n)),
            Sp, Rightarrow);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Rationals() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula X() => F.Id("X");
    private static Formula Half() => new Formula.Fraction(D(1), D(2));
    private static Formula Quarter() => new Formula.Fraction(D(1), D(4));
    private static Formula Rat(Formula n) => Call("rat", n);
    private static Formula Constant(Formula value) => Call("C", value);
    private static Formula Compose(Formula p, Formula q) => Call("comp", p, q);
    private static Formula Coeff(Formula p, Formula k) => Call("coeff", p, k);
    private static Formula Indexed(string name, Formula index) => new Formula.Subscript(F.Id(name), index);
    private static Formula Twice(Formula value) => Multiply(D(2), value);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Difference(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Multiply(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Power(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Product(Formula index, Formula domain, Formula body) =>
        Seq(new Formula.Subscript(Prod, Seq(index, Sp, InMacro, Sp, domain)), Sp, Parenthesized(body));
    private static Formula Summation(Formula index, Formula domain, Formula body) =>
        Seq(new Formula.Subscript(F.Sum, Seq(index, Sp, InMacro, Sp, domain)), Sp, Parenthesized(body));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Joined(Formula[] values, Formula separator)
    {
        List<Formula> items = [];
        for (var index = 0; index < values.Length; index++)
        {
            if (index > 0) items.AddRange([Sp, separator, Sp]);
            items.Add(values[index]);
        }
        return Seq([.. items]);
    }
    private static Formula Call(string name, params Formula[] arguments) =>
        Seq(Operatorname, Grp(F.Id(name)), Parenthesized(Joined(arguments, Comma)));
}
