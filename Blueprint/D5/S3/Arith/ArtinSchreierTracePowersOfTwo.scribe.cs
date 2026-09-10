using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class ArtinSchreierTracePowersOfTwoDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/Arith/ArtinSchreierTracePowersOfTwo.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An Artin-Schreier trace invariant proves the first parity conjecture for OEIS A396808.",
        H("A396808 Odd Exactly at Powers of Two"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("a396808-sequence"),
                DeclarationHandle.Create(Gid + "a"),
                H("The finite-prefix sequence"),
                StatementSource.FromAuthor(SequenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For each n, P_n is the polynomial containing exactly the earlier "
                        + "coefficients. The first two values are one. At every later index, "
                        + "a(n) is n times coefficient n of P_n to power n+2, minus n+1 "
                        + "times coefficient n of P_n to power n+1. This is the triangular "
                        + "finite-prefix rule extracted from the defining equation of OEIS "
                        + "A396808. The symbols mk and coeff below denote PowerSeries.mk and "
                        + "PowerSeries.coeff, with the coefficient index written first; castZ "
                        + "is the natural-to-integer cast. Thus P_n determines a(n), and "
                        + "adjoining a(n) times X to power n produces P_(n+1)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a396808-prefix-polynomial"),
                DeclarationHandle.Create(Gid + "prefixPolynomial"),
                H("The finite prefix polynomial"),
                StatementSource.FromAuthor(PrefixPolynomialFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The public prefix polynomial is initialized at zero and extends by the "
                        + "new coefficient a(n) at degree n. Consequently, the coefficient of "
                        + "X to power j in P_n is a(j) when j<n and zero otherwise."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a396808-prefix-polynomial-sum"),
                DeclarationHandle.Create(Gid + "prefixPolynomial_eq_sum"),
                H("The finite prefix is the coefficient sum"),
                StatementSource.FromAuthor(PrefixPolynomialSumFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every n, prefixPolynomial(n) is exactly the finite sum over j in "
                        + "range(n) of the constant polynomial C(a(j)) times X to power j. "
                        + "Hence the recursive and finite-sum descriptions of P_n agree."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("a396808-source-equation"),
                DeclarationHandle.Create(Gid + "source_equation"),
                H("The OEIS source equation"),
                StatementSource.FromAuthor(SourceEquationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every n greater than one, the formal power series mk(a) satisfies "
                        + "the coefficient equation in the OEIS name line. The strict-prefix "
                        + "coefficient formula isolates the contribution of a(n) to both "
                        + "powers, and the defining recurrence makes the resulting terms "
                        + "cancel."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("a396808-normalized-solution-unique"),
                DeclarationHandle.Create(Gid + "normalized_solution_unique"),
                H("Uniqueness of the normalized integer solution"),
                StatementSource.FromAuthor(NormalizedUniquenessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Any integer sequence b with b(0)=b(1)=1 and the same source equation "
                        + "at every n greater than one equals a. The proof recovers the nth "
                        + "coefficient from the strict prefix and then uses strong induction."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("a396808-artin-coefficients"),
                DeclarationHandle.Create(Gid + "artinCoeff"),
                H("The Artin-Schreier coefficient recursion"),
                StatementSource.FromAuthor(ArtinCoeffFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The public ZMod(2)-valued coefficient function starts at one, preserves "
                        + "its value on even indices by halving, and is one at an odd index "
                        + "2n+1 exactly in the n=0 branch."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a396808-artin-series"),
                DeclarationHandle.Create(Gid + "artinSeries"),
                H("The constant-one Artin-Schreier series"),
                StatementSource.FromAuthor(ArtinSeriesFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The coefficient recursion defines S over ZMod(2). It has coefficient one "
                        + "at degree zero and at exactly the powers of two, so S is "
                        + "1+x+x^2+x^4+x^8+.... Its constant term is one, while S+1 has "
                        + "constant term zero; these are the two roots of Y^2+Y=X."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a396808-artin-series-square-add"),
                DeclarationHandle.Create(Gid + "artinSeries_square_add"),
                H("The Artin-Schreier equation"),
                StatementSource.FromAuthor(ArtinSquareFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Frobenius expansion shifts the nonconstant power-of-two support. In "
                        + "characteristic two, adding S cancels every repeated coefficient and "
                        + "leaves X."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("a396808-trace-polynomial"),
                DeclarationHandle.Create(Gid + "tracePoly"),
                H("The trace-polynomial recurrence"),
                StatementSource.FromAuthor(TraceDefinitionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The polynomials T_m over ZMod(2) start at zero and one and satisfy "
                        + "T_(m+2)=T_(m+1)+X*T_m. This is the trace recurrence for the two "
                        + "roots of Y^2+Y=X."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a396808-trace-polynomial-identity"),
                DeclarationHandle.Create(Gid + "tracePoly_identity"),
                H("Trace as the sum over both roots"),
                StatementSource.FromAuthor(TraceIdentityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural exponent m, coercing T_m to a formal power series "
                        + "equals S^m+(S+1)^m. Both roots obey the same two-step power "
                        + "recurrence, which proves the identity by two-step induction. Here "
                        + "T_m is viewed as a formal power series through the coefficientwise "
                        + "embedding of polynomials."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("a396808-trace-polynomial-degree"),
                DeclarationHandle.Create(Gid + "tracePoly_natDegree_le"),
                H("Trace degree bound"),
                StatementSource.FromAuthor(TraceDegreeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The natural degree of T_m is at most the natural-number quotient m div 2. "
                        + "Here div is truncated natural division, equivalently floor(m/2); it "
                        + "is deliberately not rendered as field division."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("a396808-artin-power-coefficient-vanishing"),
                DeclarationHandle.Create(Gid + "coeff_artinSeries_pow_eq_zero"),
                H("Vanishing between half the exponent and the exponent"),
                StatementSource.FromAuthor(VanishingFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If floor(m/2)<n<m, coefficient n of S^m is zero. The degree bound kills "
                        + "coefficient n of T_m, while S+1 has zero constant coefficient and "
                        + "therefore its mth power has no coefficient below m. The trace "
                        + "identity then forces coefficient n of S^m to vanish because both "
                        + "other terms have zero nth coefficient."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("a396808-reduced-series-is-artin-series"),
                DeclarationHandle.Create(Gid + "reducedSeries_eq_artinSeries"),
                H("The reduced generating series is the constant-one root"),
                StatementSource.FromAuthor(ReducedSeriesFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Coefficientwise mapping of the integer series mk(a) through the integer "
                        + "cast into ZMod(2) equals S. Both sides have constant and linear "
                        + "coefficients one and satisfy the mod-two source equation; triangular "
                        + "coefficient induction gives uniqueness. The intCast argument records "
                        + "the ring homomorphism from the integers into ZMod(2)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("a396808-first-conjecture"),
                DeclarationHandle.Create(Gid + "a396808_first_conjecture"),
                H("Odd coefficients occur exactly at powers of two"),
                StatementSource.FromAuthor(FirstConjectureFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "OEIS A396808 states this as its first conjecture. For every positive "
                        + "natural index n, the integer a(n) is odd if and only if n=2^r for "
                        + "some natural exponent r. The reduction theorem identifies its parity "
                        + "with the exact support of the constant-one root."))),
                DescribeRole.Theorem))));

    private static Formula SequenceFormula()
    {
        Formula n = F.Id("n");
        Formula p = Call("prefixPolynomial", n);
        Formula later = Difference(
            Product(CastZ(n), Coeff(n, Power(p, Add(n, D(2))))),
            Product(Parenthesized(Add(CastZ(n), D(1))),
                Coeff(n, Power(p, Add(n, D(1))))));
        return Disp(new Formula.Aligned([
            Seq(F.Id("a"), Colon, Sp, Naturals(), Sp, To, Sp, Integers(), Comma),
            Seq(Bound(n), Equal(A(n), Call("ite", Less(n, D(2)), D(1), later))),
        ]));
    }

    private static Formula PrefixPolynomialFormula()
    {
        Formula n = F.Id("n");
        return Disp(new Formula.Aligned([
            Seq(F.Id("prefixPolynomial"), Colon, Sp, Naturals(), Sp, To, Sp,
                Seq(Integers(), OpenBracket, F.Id("X"), CloseBracket), Comma),
            Equal(Call("prefixPolynomial", D(0)), D(0)),
            Seq(Bound(n), Equal(Call("prefixPolynomial", Add(n, D(1))),
                Add(Call("prefixPolynomial", n), Product(A(n), Power(F.Id("X"), n))))),
        ]));
    }

    private static Formula PrefixPolynomialSumFormula()
    {
        Formula n = F.Id("n");
        Formula j = F.Id("j");
        Formula sum = FiniteSum(j, Call("range", n),
            Product(Call("C", A(j)), Power(F.Id("X"), j)));
        return Disp(Seq(Bound(n), Equal(Call("prefixPolynomial", n), sum)));
    }

    private static Formula SourceEquationFormula()
    {
        Formula n = F.Id("n");
        Formula series = Call("mk", F.Id("a"));
        return Disp(Seq(
            Bound(n), Parenthesized(Less(D(1), n)), Sp, Rightarrow, Sp,
            Equal(
                Product(Parenthesized(Add(CastZ(n), D(1))),
                    Coeff(n, Power(series, Add(n, D(1))))),
                Product(CastZ(n), Coeff(n, Power(series, Add(n, D(2))))))));
    }

    private static Formula NormalizedUniquenessFormula()
    {
        Formula b = F.Id("b");
        Formula n = F.Id("n");
        Formula series = Call("mk", b);
        Formula source = Seq(
            Bound(n), Parenthesized(Less(D(1), n)), Sp, Rightarrow, Sp,
            Equal(
                Product(Parenthesized(Add(CastZ(n), D(1))),
                    Coeff(n, Power(series, Add(n, D(1))))),
                Product(CastZ(n), Coeff(n, Power(series, Add(n, D(2)))))));
        Formula hypotheses = Parenthesized(Seq(
            Parenthesized(Equal(Call("b", D(0)), D(1))), Sp, Land, Sp,
            Parenthesized(Seq(
                Parenthesized(Equal(Call("b", D(1)), D(1))), Sp, Land, Sp,
                Parenthesized(source)))));
        return Disp(Seq(
            Forall, Sp, b, Colon, Sp,
            Parenthesized(Seq(Naturals(), Sp, To, Sp, Integers())), Comma, Sp,
            hypotheses, Sp, Rightarrow, Sp, Equal(b, F.Id("a"))));
    }

    private static Formula ArtinCoeffFormula()
    {
        Formula n = F.Id("n");
        return Disp(new Formula.Aligned([
            Seq(F.Id("artinCoeff"), Colon, Sp, Naturals(), Sp, To, Sp,
                Call("ZMod", D(2)), Comma),
            Equal(Call("artinCoeff", D(0)), D(1)),
            Seq(Bound(n), Equal(Call("artinCoeff", Product(D(2), n)),
                Call("artinCoeff", n))),
            Seq(Bound(n), Equal(Call("artinCoeff", Add(Product(D(2), n), D(1))),
                Call("ite", Equal(n, D(0)), D(1), D(0)))),
        ]));
    }

    private static Formula ArtinSeriesFormula()
    {
        return Disp(new Formula.Aligned([
            Seq(F.Id("S"), Colon, Sp, ModTwoSeries(), Comma),
            Equal(F.Id("S"), Call("mk", F.Id("artinCoeff"))),
        ]));
    }

    private static Formula ArtinSquareFormula() =>
        Disp(Equal(Add(Power(F.Id("S"), D(2)), F.Id("S")), F.Id("X")));

    private static Formula TraceDefinitionFormula()
    {
        Formula m = F.Id("m");
        return Disp(new Formula.Aligned([
            Seq(F.Id("T"), Colon, Sp, Naturals(), Sp, To, Sp, PolynomialModTwo(), Comma),
            Equal(Indexed("T", D(0)), D(0)),
            Equal(Indexed("T", D(1)), D(1)),
            Seq(Bound(m), Equal(Indexed("T", Add(m, D(2))),
                Add(Indexed("T", Add(m, D(1))),
                    Product(F.Id("X"), Indexed("T", m))))),
        ]));
    }

    private static Formula TraceIdentityFormula()
    {
        Formula m = F.Id("m");
        return Disp(Seq(
            Bound(m),
            Equal(Call("coe", Indexed("T", m)),
                Add(Power(F.Id("S"), m),
                    Power(Parenthesized(Add(F.Id("S"), D(1))), m)))));
    }

    private static Formula TraceDegreeFormula()
    {
        Formula m = F.Id("m");
        return Disp(Seq(
            Bound(m),
            AtMost(Call("natDegree", Indexed("T", m)), Call("div", m, D(2)))));
    }

    private static Formula VanishingFormula()
    {
        Formula m = F.Id("m");
        Formula n = F.Id("n");
        return Disp(Seq(
            Bound(m, n),
            Parenthesized(Less(Call("div", m, D(2)), n)), Sp, Rightarrow, Sp,
            Parenthesized(Less(n, m)), Sp, Rightarrow, Sp,
            Equal(Coeff(n, Power(F.Id("S"), m)), D(0))));
    }

    private static Formula ReducedSeriesFormula() =>
        Disp(Equal(
            Call("map", Call("intCast", Call("ZMod", D(2))), Call("mk", F.Id("a"))),
            F.Id("S")));

    private static Formula FirstConjectureFormula()
    {
        Formula n = F.Id("n");
        Formula r = F.Id("r");
        Formula powerWitness = Seq(
            Exists, Sp, r, Colon, Sp, Naturals(), Comma, Sp,
            Equal(n, Power(D(2), r)));
        return Disp(Seq(
            Bound(n), Parenthesized(Less(D(0), n)), Sp, Rightarrow, Sp,
            Parenthesized(Seq(
                Call("Odd", A(n)), Sp, Leftrightarrow, Sp,
                Parenthesized(powerWitness)))));
    }

    private static Formula FiniteSum(Formula index, Formula set, Formula summand) =>
        Seq(new Formula.Subscript(F.Sum, Seq(index, Sp, InMacro, Sp, set)), Sp, summand);

    private static Formula A(Formula n) => Call("a", n);
    private static Formula Coeff(Formula n, Formula series) => Call("coeff", n, series);
    private static Formula CastZ(Formula n) => Call("castZ", n);
    private static Formula Indexed(string name, Formula index) =>
        new Formula.Subscript(F.Id(name), index);
    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Difference(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Product(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula PolynomialModTwo() =>
        Seq(Call("ZMod", D(2)), OpenBracket, F.Id("X"), CloseBracket);
    private static Formula ModTwoSeries() =>
        Seq(Call("ZMod", D(2)), OpenBracket, OpenBracket,
            F.Id("X"), CloseBracket, CloseBracket);
    private static Formula Bound(params Formula[] variables) =>
        Seq(Forall, Sp, Joined(variables, Comma), Colon, Sp, Naturals(), Comma, Sp);
    private static Formula Joined(Formula[] values, Formula separator)
    {
        var items = new List<Formula>();
        for (var i = 0; i < values.Length; i++)
        {
            if (i > 0)
            {
                items.Add(separator);
                items.Add(Sp);
            }
            items.Add(values[i]);
        }
        return Seq([.. items]);
    }
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
