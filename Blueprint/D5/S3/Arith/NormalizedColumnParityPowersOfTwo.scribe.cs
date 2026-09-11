using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class NormalizedColumnParityPowersOfTwoDocument :
    IScribeDocumentDefinition
{
    private const string Gid =
        "D5/S3/Arith/NormalizedColumnParityPowersOfTwo.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The zero-constant-coefficient solution of the cubic equation recorded for A144637 is integral and odd exactly at positive powers of two.",
        H("A144637 Normalized Column Parity"),
        Blocks(
            Paragraph(Text(
                "The series treated here is the unique power series with zero constant "
                    + "coefficient satisfying 36y^3+3y^2+(1+6x)y=x^2. OEIS A144637 records "
                    + "that its exponential generating function A satisfies this equation "
                    + "through y=(1/18)A(6x), so that coefficient n of y would equal "
                    + "6^n a(n)/(18 n!). That identification is quoted from the entry and is "
                    + "not proved below; every statement below concerns only the series "
                    + "defined by the equation.")),
            Describe.Lean(
                DescribeId.Create("a144637-normalized-integral-series"),
                DeclarationHandle.Create(Gid + "normalizedColumnSeries"),
                H("The normalized integral series"),
                StatementSource.FromAuthor(SeriesFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The integer series y is built by a finite-prefix recursion. At degree n, "
                        + "the coefficients of the square and cube depend only on degrees below "
                        + "n because the constant coefficient is zero. The coefficient of y in "
                        + "1+6x is one, so the degree-n equation determines the next integer "
                        + "coefficient without division. This construction records integrality "
                        + "in the coefficient type itself."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a144637-normalized-column-parity"),
                DeclarationHandle.Create(Gid + "a144637_normalized_column_parity"),
                H("Odd coefficients occur exactly at positive powers of two"),
                StatementSource.FromAuthor(ParityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The theorem proves at once that y has constant coefficient zero, "
                            + "satisfies the complete cubic equation, and is the unique integer "
                            + "power-series solution with that constant coefficient. It then "
                            + "states the parity equivalence for every natural index, including "
                            + "the zero and one boundary cases.")),
                    Paragraph(Text(
                        "Reducing the cubic equation modulo two removes the terms multiplied by "
                            + "36 and 6 and changes the coefficient 3 to one. The result is "
                            + "y^2+y=x^2. The general characteristic-two uniqueness theorem "
                            + "identifies this zero-constant root with x^2+x^4+x^8+.... The "
                            + "Frobenius square doubles every exponent, so its support consists "
                            + "exactly of 2^k for k at least one. Reduction of an integer to one "
                            + "modulo two is equivalent to oddness, giving both directions. This "
                            + "is a symbolic proof with no bounded enumeration or checker."))),
                DescribeRole.Theorem))));

    private static Formula SeriesFormula() => Disp(Seq(
        F.Id("normalizedColumnSeries"), Colon, Sp, Series(), Comma, Sp,
        Equal(F.Id("normalizedColumnSeries"), Call("mk", F.Id("normalizedCoeff")))));

    private static Formula ParityFormula()
    {
        Formula y = F.Id("normalizedColumnSeries");
        Formula z = F.Id("z");
        Formula n = F.Id("n");
        Formula k = F.Id("k");
        Formula zeroConstant = Equal(Call("constantCoeff", y), D(0));
        Formula equation = CubicEquation(y);
        Formula uniqueness = Seq(
            Forall, Sp, z, Colon, Sp, Series(), Comma, Sp,
            Parenthesized(Equal(Call("constantCoeff", z), D(0))), Sp, Rightarrow, Sp,
            Parenthesized(CubicEquation(z)), Sp, Rightarrow, Sp, Equal(z, y));
        Formula support = Seq(
            Exists, Sp, k, Colon, Sp, Naturals(), Comma, Sp,
            Parenthesized(Seq(D(1), Sp, Le, Sp, k)), Sp, Land, Sp,
            Parenthesized(Equal(n, Pow(D(2), k))));
        Formula parity = Seq(
            Forall, Sp, n, Colon, Sp, Naturals(), Comma, Sp,
            Call("Odd", Call("coeff", n, y)), Sp, Iff, Sp, support);

        return Disp(And(zeroConstant,
            And(equation, And(Parenthesized(uniqueness), parity))));
    }

    private static Formula CubicEquation(Formula value)
    {
        Formula x = F.Id("X");
        Formula cubic = Add(
            Mul(D(3, 6), Pow(value, D(3))),
            Add(
                Mul(D(3), Pow(value, D(2))),
                Mul(Add(D(1), Mul(D(6), x)), value)));
        return Equal(cubic, Pow(x, D(2)));
    }

    private static Formula Series() => Call("PowerSeries", Integers());
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Pow(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);

    private static Formula Equal(Formula left, Formula right) =>
        Seq(left, Sp, Eq, Sp, right);

    private static Formula And(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
