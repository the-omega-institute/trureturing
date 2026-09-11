using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class RationalCompositionParityPeriodTenDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/RationalCompositionParityPeriodTen.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Formula (2) for OEIS A396093 determines an integer sequence whose parity has period ten.",
        H("A396093 Parity Period Ten"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("a396093-numerator"),
                DeclarationHandle.Create(Prefix + "N"),
                H("Factored numerator of formula (2)"),
                StatementSource.FromAuthor(NDefinitionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Proof: (definition). N is formula (2)'s literal factored "
                        + "numerator in Q[[x]]. Its factors are x, (1-x)^2, and "
                        + "(1-3x+x^2)^2."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a396093-denominator"),
                DeclarationHandle.Create(Prefix + "D"),
                H("Squared denominator of formula (2)"),
                StatementSource.FromAuthor(DDefinitionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Proof: (definition). D is formula (2)'s literal squared "
                        + "quartic denominator in Q[[x]]. Squaring the quartic produces a "
                        + "degree-eight denominator with constant coefficient one."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a396093-denominator-expansion"),
                DeclarationHandle.Create(Prefix + "denominator_expansion"),
                H("Denominator expansion"),
                StatementSource.FromAuthor(DenominatorExpansionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Normalization: simp unfolds D and ring gives the "
                        + "nine coefficients. These coefficients determine the convolution "
                        + "formula for multiplying a power series by D."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("a396093-numerator-expansion"),
                DeclarationHandle.Create(Prefix + "numerator_expansion"),
                H("Numerator expansion"),
                StatementSource.FromAuthor(NumeratorExpansionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Normalization: simp unfolds N and ring gives the "
                        + "eight initial coefficients. They supply the right-hand sides of the "
                        + "coefficient equations in degrees zero through seven."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("a396093-sequence"),
                DeclarationHandle.Create(Prefix + "a"),
                H("The recurrence-defined integer sequence"),
                StatementSource.FromAuthor(SequenceDefinitionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Proof: (definition). The sequence a is defined by the "
                        + "order-eight recurrence with its eight initial values; it is not "
                        + "stipulated by parity or by a finite table. Its later values are "
                        + "therefore determined uniquely from the preceding eight values."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a396093-rational-tail-equation"),
                DeclarationHandle.Create(Prefix + "rational_tail_equation"),
                H("Homogeneous coefficient equations"),
                StatementSource.FromAuthor(RationalTailFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Proof: linear normalization of the order-eight recurrence gives the "
                        + "coefficient equations above degree seven. Rearranging the recurrence "
                        + "places every term on the left and yields zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("a396093-initial-coefficient-equations"),
                DeclarationHandle.Create(Prefix + "initial_coefficient_equations"),
                H("Inhomogeneous coefficient equations"),
                StatementSource.FromAuthor(InitialEquationsFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Proof: norm_num substitutes the eight initial values into the convolution "
                        + "equations for multiplication by D. This gives the inhomogeneous "
                        + "coefficient equations in degrees zero through seven."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("a396093-generating-function-identity"),
                DeclarationHandle.Create(Prefix + "generating_function_identity"),
                H("Generating-function product identity"),
                StatementSource.FromAuthor(GeneratingFunctionIdentityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Proof: coefficient extensionality reduces the power-series identity to "
                        + "equality in each degree. The recurrence supplies the homogeneous tail "
                        + "equations above degree seven, while the eight initial equations and "
                        + "the expansions of D and N settle degrees zero through seven."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("a396093-generating-function"),
                DeclarationHandle.Create(Prefix + "generating_function"),
                H("Generating function in division form"),
                StatementSource.FromAuthor(GeneratingFunctionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Proof: power-series inversion rewrites the product identity, "
                        + "and the expanded denominator proves its constant coefficient is one. "
                        + "Consequently D is invertible and A(x)D(x)=N(x) becomes "
                        + "A(x)=N(x)D(x)^-1."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("a396093-coefficients-unique"),
                DeclarationHandle.Create(Prefix + "coefficients_unique"),
                H("Formula (2) uniquely determines its integer coefficients"),
                StatementSource.FromAuthor(CoefficientsUniqueFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Proof: comparing coefficients in b(x)D(x)=N(x) and a(x)D(x)=N(x) gives "
                        + "the same convolution equation for b and a. Strong induction, using "
                        + "equality of earlier coefficients and the constant coefficient one of "
                        + "D, gives b(n)=a(n) for every n."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("a396093-reduced-recurrence"),
                DeclarationHandle.Create(Prefix + "reduced_recurrence"),
                H("Characteristic-two recurrence"),
                StatementSource.FromAuthor(ReducedRecurrenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Proof: casting the integer recurrence to characteristic two makes the "
                        + "coefficients 14 and 196 vanish and makes 75 and 269 equal one. Since "
                        + "negation is the identity, the surviving terms are exactly the four "
                        + "even lags."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("a396093-parity-period-ten"),
                DeclarationHandle.Create(Prefix + "parity_period_ten"),
                H("Period ten modulo two"),
                StatementSource.FromAuthor(PeriodTenFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Proof: two shifted reduced recurrences cancel in "
                        + "characteristic two. Substituting the recurrence at n into the one at "
                        + "n+2 makes every intermediate term occur twice, leaving "
                        + "a(n+10)=a(n)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("a396093-odd-residue-characterization"),
                DeclarationHandle.Create(Prefix + "odd_iff_mod_ten"),
                H("Odd values exactly in four residue classes"),
                StatementSource.FromAuthor(OddIffFormula("a")),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Proof: period ten reduces every index to one of the first ten residues. "
                        + "Direct evaluation of those ten values gives odd terms precisely at "
                        + "residues 1, 3, 7, and 9."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("a396093-odd-gf-characterization"),
                DeclarationHandle.Create(Prefix + "odd_iff_mod_ten_of_generating_function"),
                H("Parity for the formula (2) coefficient sequence"),
                StatementSource.FromAuthor(OddIffGeneratingFunctionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Proof: coefficients_unique rewrites the sequence and the "
                        + "period-ten residue theorem closes the result. Thus every integer "
                        + "coefficient sequence satisfying formula (2) has the same parity "
                        + "pattern."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("a396093-even-even-index"),
                DeclarationHandle.Create(Prefix + "even_at_even_index"),
                H("Even values at positive even indices"),
                StatementSource.FromAuthor(EvenIndexFormula("a")),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Proof: modular arithmetic projects the first OEIS "
                        + "conjecture from the residue characterization. An even index has an "
                        + "even residue modulo ten, so it never lies in the four odd residue "
                        + "classes."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("a396093-even-odd-index-iff"),
                DeclarationHandle.Create(Prefix + "even_at_odd_index_iff"),
                H("Even values at odd indices"),
                StatementSource.FromAuthor(EvenOddIndexFormula("a")),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Proof: modular arithmetic projects the second OEIS "
                        + "conjecture from the residue characterization. Natural subtraction is "
                        + "truncated at zero. For n at least one, a(2n-1) is even exactly when "
                        + "n is congruent to 3 modulo 5, equivalently n=5k-2 for some k at least "
                        + "one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("a396093-even-even-index-gf"),
                DeclarationHandle.Create(Prefix + "even_at_even_index_of_generating_function"),
                H("First conjecture for formula (2) coefficients"),
                StatementSource.FromAuthor(EvenIndexGeneratingFunctionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Proof: coefficient uniqueness gives b(2n)=a(2n), and the even-index "
                        + "result for a then proves that b(2n) is even."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("a396093-even-odd-index-gf"),
                DeclarationHandle.Create(Prefix + "even_at_odd_index_iff_of_generating_function"),
                H("Second conjecture for formula (2) coefficients"),
                StatementSource.FromAuthor(EvenOddIndexGeneratingFunctionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Proof: coefficient uniqueness gives b(2n-1)=a(2n-1), so the odd-index "
                        + "characterization for a transfers the stated equivalence to b."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("a396093-basic-rational-map"),
                DeclarationHandle.Create(Prefix + "Bf"),
                H("Basic rational-function map"),
                StatementSource.FromAuthor(BfFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Proof: (definition). OEIS A396093 states B(x)=x/(1-x)^2. "
                        + "Here Bf is that total field operation on Q(x). Thus Bf(y) is defined "
                        + "for every rational function y, including when 1-y is zero."))),
                DescribeRole.Definition),
            Paragraph(Text(
                "The sequence a is defined by the order-eight recurrence with its eight initial "
                    + "values; Theorem generating_function identifies it with the coefficient "
                    + "sequence of formula (2), Theorem coefficients_unique shows formula (2) "
                    + "determines it, and direct rational-function normalization identifies formula (2) "
                    + "with B(B(B(x))) in Q(x). The three together tie a to the OEIS definition.")))));

    private static Formula NDefinitionFormula()
    {
        Formula x = F.Id("x");
        return Disp(Seq(F.Id("N"), Colon, Sp, RationalPowerSeries(), Comma, Sp,
            Parenthesized(Equal(F.Id("N"), NumeratorFactored(x))), Dot));
    }

    private static Formula DDefinitionFormula()
    {
        Formula x = F.Id("x");
        return Disp(Seq(F.Id("D"), Colon, Sp, RationalPowerSeries(), Comma, Sp,
            Parenthesized(Equal(F.Id("D"), DenominatorSquared(x))), Dot));
    }

    private static Formula DenominatorExpansionFormula()
    {
        Formula x = F.Id("x");
        Formula expanded = Subtract(D(1), Product(D(1, 4), x));
        expanded = Add(expanded, Product(D(7, 5), Power(x, 2)));
        expanded = Subtract(expanded, Product(D(1, 9, 6), Power(x, 3)));
        expanded = Add(expanded, Product(D(2, 6, 9), Power(x, 4)));
        expanded = Subtract(expanded, Product(D(1, 9, 6), Power(x, 5)));
        expanded = Add(expanded, Product(D(7, 5), Power(x, 6)));
        expanded = Subtract(expanded, Product(D(1, 4), Power(x, 7)));
        expanded = Add(expanded, Power(x, 8));
        return Disp(Equal(F.Id("D"), expanded));
    }

    private static Formula NumeratorExpansionFormula()
    {
        Formula x = F.Id("x");
        Formula expanded = Subtract(x, Product(D(8), Power(x, 2)));
        expanded = Add(expanded, Product(D(2, 4), Power(x, 3)));
        expanded = Subtract(expanded, Product(D(3, 4), Power(x, 4)));
        expanded = Add(expanded, Product(D(2, 4), Power(x, 5)));
        expanded = Subtract(expanded, Product(D(8), Power(x, 6)));
        expanded = Add(expanded, Power(x, 7));
        return Disp(Equal(F.Id("N"), expanded));
    }

    private static Formula SequenceDefinitionFormula()
    {
        Formula n = F.Id("n");
        Formula[] clauses =
        [
            Equal(A(D(0)), D(0)),
            Equal(A(D(1)), D(1)),
            Equal(A(D(2)), D(6)),
            Equal(A(D(3)), D(3, 3)),
            Equal(A(D(4)), D(1, 7, 4)),
            Equal(A(D(5)), D(8, 9, 2)),
            Equal(A(D(6)), D(4, 4, 8, 0)),
            Equal(A(D(7)), D(2, 2, 1, 4, 9)),
            ForAll("n", Naturals(), ARecurrenceEquation(n)),
        ];
        return Disp(Seq(F.Id("a"), Colon, Sp, FunctionType(Naturals(), Integers()),
            Comma, Sp, Parenthesized(AndMany(clauses)), Dot));
    }

    private static Formula RationalTailFormula()
    {
        Formula n = F.Id("n");
        Formula expression = Add(
            Subtract(
                Add(
                    Subtract(
                        Add(
                            Subtract(
                                Add(
                                    Subtract(A(Add(n, D(8))), Product(D(1, 4), A(Add(n, D(7))))),
                                    Product(D(7, 5), A(Add(n, D(6))))),
                                Product(D(1, 9, 6), A(Add(n, D(5))))),
                            Product(D(2, 6, 9), A(Add(n, D(4))))),
                        Product(D(1, 9, 6), A(Add(n, D(3))))),
                    Product(D(7, 5), A(Add(n, D(2))))),
                Product(D(1, 4), A(Add(n, D(1))))),
            A(n));
        return Disp(ForAll("n", Naturals(), Equal(expression, D(0))));
    }

    private static Formula InitialEquationsFormula()
    {
        Formula[] equations =
        [
            Equal(A(D(0)), D(0)),
            Equal(Subtract(A(D(1)), Product(D(1, 4), A(D(0)))), D(1)),
            Equal(Add(Subtract(A(D(2)), Product(D(1, 4), A(D(1)))),
                Product(D(7, 5), A(D(0)))), Negative(D(8))),
            Equal(Subtract(Add(Subtract(A(D(3)), Product(D(1, 4), A(D(2)))),
                Product(D(7, 5), A(D(1)))), Product(D(1, 9, 6), A(D(0)))), D(2, 4)),
            Equal(Add(Subtract(Add(Subtract(A(D(4)), Product(D(1, 4), A(D(3)))),
                Product(D(7, 5), A(D(2)))), Product(D(1, 9, 6), A(D(1)))),
                Product(D(2, 6, 9), A(D(0)))), Negative(D(3, 4))),
            Equal(Subtract(Add(Subtract(Add(Subtract(A(D(5)), Product(D(1, 4), A(D(4)))),
                Product(D(7, 5), A(D(3)))), Product(D(1, 9, 6), A(D(2)))),
                Product(D(2, 6, 9), A(D(1)))), Product(D(1, 9, 6), A(D(0)))), D(2, 4)),
            Equal(Add(Subtract(Add(Subtract(Add(Subtract(A(D(6)),
                Product(D(1, 4), A(D(5)))), Product(D(7, 5), A(D(4)))),
                Product(D(1, 9, 6), A(D(3)))), Product(D(2, 6, 9), A(D(2)))),
                Product(D(1, 9, 6), A(D(1)))), Product(D(7, 5), A(D(0)))), Negative(D(8))),
            Equal(Subtract(Add(Subtract(Add(Subtract(Add(Subtract(A(D(7)),
                Product(D(1, 4), A(D(6)))), Product(D(7, 5), A(D(5)))),
                Product(D(1, 9, 6), A(D(4)))), Product(D(2, 6, 9), A(D(3)))),
                Product(D(1, 9, 6), A(D(2)))), Product(D(7, 5), A(D(1)))),
                Product(D(1, 4), A(D(0)))), D(1)),
        ];
        return Disp(AndMany(equations));
    }

    private static Formula GeneratingFunctionIdentityFormula()
    {
        Formula x = F.Id("x");
        return Disp(Equal(Product(SeriesOf("a"), DenominatorSquared(x)), NumeratorFactored(x)));
    }

    private static Formula GeneratingFunctionFormula()
    {
        Formula x = F.Id("x");
        return Disp(Equal(SeriesOf("a"),
            Product(NumeratorFactored(x), Inverse(DenominatorSquared(x)))));
    }

    private static Formula CoefficientsUniqueFormula()
    {
        Formula b = F.Id("b");
        Formula n = F.Id("n");
        Formula x = F.Id("x");
        Formula hypothesis = Equal(Product(SeriesOf("b"), DenominatorSquared(x)),
            NumeratorFactored(x));
        Formula conclusion = ForAll("n", Naturals(), Equal(Call("b", n), A(n)));
        return Disp(ForAll("b", FunctionType(Naturals(), Integers()),
            Implies(Parenthesized(hypothesis), conclusion)));
    }

    private static Formula ARecurrenceEquation(Formula n)
    {
        Formula right = Subtract(Product(D(1, 4), A(Add(n, D(7)))),
            Product(D(7, 5), A(Add(n, D(6)))));
        right = Add(right, Product(D(1, 9, 6), A(Add(n, D(5)))));
        right = Subtract(right, Product(D(2, 6, 9), A(Add(n, D(4)))));
        right = Add(right, Product(D(1, 9, 6), A(Add(n, D(3)))));
        right = Subtract(right, Product(D(7, 5), A(Add(n, D(2)))));
        right = Add(right, Product(D(1, 4), A(Add(n, D(1)))));
        right = Subtract(right, A(n));
        return Equal(A(Add(n, D(8))), right);
    }

    private static Formula ReducedRecurrenceFormula()
    {
        Formula n = F.Id("n");
        Formula right = SumMany(CastModTwo(A(n)), CastModTwo(A(Add(n, D(2)))),
            CastModTwo(A(Add(n, D(4)))), CastModTwo(A(Add(n, D(6)))));
        return Disp(ForAll("n", Naturals(), Equal(CastModTwo(A(Add(n, D(8)))), right)));
    }

    private static Formula PeriodTenFormula()
    {
        Formula n = F.Id("n");
        return Disp(ForAll("n", Naturals(),
            Equal(CastModTwo(A(Add(n, D(1, 0)))), CastModTwo(A(n)))));
    }

    private static Formula OddIffFormula(string sequence)
    {
        Formula n = F.Id("n");
        Formula residue = new Formula.Modulo(n, D(1, 0));
        Formula membership = Member(residue, new Formula.SetLiteral([D(1), D(3), D(7), D(9)]));
        return Disp(ForAll("n", Naturals(),
            Iff(Call("Odd", Call(sequence, n)), membership)));
    }

    private static Formula OddIffGeneratingFunctionFormula()
    {
        Formula b = F.Id("b");
        Formula n = F.Id("n");
        Formula x = F.Id("x");
        Formula hypothesis = Equal(Product(SeriesOf("b"), DenominatorSquared(x)),
            NumeratorFactored(x));
        Formula residue = new Formula.Modulo(n, D(1, 0));
        Formula membership = Member(residue, new Formula.SetLiteral([D(1), D(3), D(7), D(9)]));
        Formula conclusion = ForAll("n", Naturals(),
            Iff(Call("Odd", Call("b", n)), membership));
        return Disp(ForAll("b", FunctionType(Naturals(), Integers()),
            Implies(Parenthesized(hypothesis), conclusion)));
    }

    private static Formula EvenIndexFormula(string sequence)
    {
        Formula n = F.Id("n");
        return Disp(ForAll("n", Naturals(), Implies(LessOrEqual(D(1), n),
            Call("Even", Call(sequence, Product(D(2), n))))));
    }

    private static Formula EvenOddIndexFormula(string sequence)
    {
        Formula n = F.Id("n");
        Formula k = F.Id("k");
        Formula witness = Exists("k", Naturals(), And(LessOrEqual(D(1), k),
            Equal(n, Subtract(Product(D(5), k), D(2)))));
        Formula conclusion = Iff(
            Call("Even", Call(sequence, Subtract(Product(D(2), n), D(1)))), witness);
        return Disp(ForAll("n", Naturals(), Implies(LessOrEqual(D(1), n), conclusion)));
    }

    private static Formula EvenIndexGeneratingFunctionFormula()
    {
        Formula b = F.Id("b");
        Formula x = F.Id("x");
        Formula hypothesis = Equal(Product(SeriesOf("b"), DenominatorSquared(x)),
            NumeratorFactored(x));
        return Disp(ForAll("b", FunctionType(Naturals(), Integers()),
            Implies(Parenthesized(hypothesis), EvenIndexFormulaBody("b"))));
    }

    private static Formula EvenOddIndexGeneratingFunctionFormula()
    {
        Formula b = F.Id("b");
        Formula x = F.Id("x");
        Formula hypothesis = Equal(Product(SeriesOf("b"), DenominatorSquared(x)),
            NumeratorFactored(x));
        return Disp(ForAll("b", FunctionType(Naturals(), Integers()),
            Implies(Parenthesized(hypothesis), EvenOddIndexFormulaBody("b"))));
    }

    private static Formula EvenIndexFormulaBody(string sequence)
    {
        Formula n = F.Id("n");
        return ForAll("n", Naturals(), Implies(LessOrEqual(D(1), n),
            Call("Even", Call(sequence, Product(D(2), n)))));
    }

    private static Formula EvenOddIndexFormulaBody(string sequence)
    {
        Formula n = F.Id("n");
        Formula k = F.Id("k");
        Formula witness = Exists("k", Naturals(), And(LessOrEqual(D(1), k),
            Equal(n, Subtract(Product(D(5), k), D(2)))));
        return ForAll("n", Naturals(), Implies(LessOrEqual(D(1), n),
            Iff(Call("Even", Call(sequence, Subtract(Product(D(2), n), D(1)))), witness)));
    }

    private static Formula BfFormula()
    {
        Formula y = F.Id("y");
        return Disp(ForAll("y", RationalFunctions(), Equal(Call("Bf", y),
            new Formula.Fraction(y, Power(Parenthesized(Subtract(D(1), y)), 2)))));
    }

    private static Formula SeriesOf(string sequence)
    {
        Formula n = F.Id("n");
        Formula lambda = Seq(n, Sp, Mapsto, Sp, CastToRationals(Call(sequence, n)));
        return Call("mk", Parenthesized(lambda));
    }

    private static Formula DenominatorQuartic(Formula x) =>
        Add(Subtract(Add(Subtract(D(1), Product(D(7), x)),
            Product(D(1, 3), Power(x, 2))), Product(D(7), Power(x, 3))), Power(x, 4));

    private static Formula DenominatorSquared(Formula x) =>
        Power(Parenthesized(DenominatorQuartic(x)), 2);

    private static Formula NumeratorFactored(Formula x) =>
        Product(Product(x, Power(Parenthesized(Subtract(D(1), x)), 2)),
            Power(Parenthesized(Add(Subtract(D(1), Product(D(3), x)), Power(x, 2))), 2));

    private static Formula Inverse(Formula value) =>
        new Formula.Power(Parenthesized(value), Negative(D(1)));
    private static Formula A(Formula index) => Call("a", index);
    private static Formula CastModTwo(Formula value) => Call("cast", value, Call("ZMod", D(2)));
    private static Formula CastToRationals(Formula value) => Call("cast", value, Rationals());
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula FunctionType(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Rationals() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula RationalPowerSeries() =>
        Seq(Rationals(), OpenBracket, OpenBracket, F.Id("x"), CloseBracket, CloseBracket);
    private static Formula RationalFunctions() => Seq(Rationals(), Parenthesized(F.Id("x")));
    private static Formula Power(Formula value, byte exponent) =>
        new Formula.Power(value, D(exponent));
    private static Formula Negative(Formula value) => new Formula.Negate(value);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Product(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Member(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula ForAll(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Exists(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(variable), domain, body);

    private static Formula SumMany(params Formula[] terms)
    {
        Formula result = terms[0];
        foreach (Formula term in terms[1..])
        {
            result = Add(result, term);
        }
        return result;
    }

    private static Formula AndMany(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (int i = clauses.Length - 2; i >= 0; i--)
        {
            result = And(clauses[i], result);
        }
        return result;
    }

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
