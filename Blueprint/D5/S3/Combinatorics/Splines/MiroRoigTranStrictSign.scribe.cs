using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Splines;

internal sealed class MiroRoigTranStrictSignDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Splines/MiroRoigTranStrictSign.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/miroroigtran2020weak");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal Miró-Roig--Tran alternating integer coefficient is strictly negative for "
            + "every natural n at least two.",
        H("The Miró-Roig--Tran Strict-Sign Conjecture"),
        Blocks(
            Paragraph(Text(
                "The source conjecture appears immediately after Proposition 3.12. Its quantifier "
                    + "is every n>=2. The separate n>=4 assumption in Proposition 3.12(c) governs "
                    + "a preceding weak-Lefschetz implication and does not restrict the displayed "
                    + "conjecture. The formal target is the coefficient itself: no monotonicity "
                    + "suggestion, WLP consequence, bounded check, or non-strict proxy is substituted.")),
            Describe.Lean(
                DescribeId.Create("miro-roig-tran-coefficient"),
                DeclarationHandle.Create(Prefix + "coefficient"),
                H("The literal alternating integer coefficient"),
                StatementSource.FromAuthor(CoefficientFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For natural n, coefficient(n) is the integer sum over k=0,...,n of "
                        + "(-1)^k binom(2n+2,k) times "
                        + "(2n^2-1-(2n-1)k)^(2n-1). The affine subtraction and exponentiation "
                        + "take place in the integers exactly as in the formal declaration."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("miro-roig-tran-strict-sign"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Strict negativity for every n at least two"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For every natural n>=2, the literal integer coefficient is strictly "
                            + "negative. In particular n=2 is included; direct evaluation gives "
                            + "coefficient(2)=-26.")),
                    Paragraph(Text(
                        "The proof sets m=2n+2 and x=(2n^2-1)/(2n-1). Terms with k>n have "
                            + "nonpositive positive-part arguments and vanish. Factoring the "
                            + "positive denominator from the remaining terms yields the exact "
                            + "normalization")),
                    Paragraph(Math(NormalizationFormula())),
                    Paragraph(Text(
                        "where C is the normalized finite positive-part curvature from the "
                            + "recurrence owner. Since n>=2, m>=6 and x lies in the closed core "
                            + "[s_m,m-s_m]. The strict-curvature theorem therefore makes C_m(x) "
                            + "negative, while both scale factors are positive. For n=2 the point "
                            + "is x=7/3, the left closed-core endpoint of C_6, so endpoint "
                            + "strictness is essential. Casting the resulting real inequality "
                            + "back to the integers proves the stated sign."))),
                DescribeRole.Theorem))));

    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula N => F.Id("n");
    private static Formula K => F.Id("k");

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);

    private static Formula Paren(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Pow(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula TwoNMinusOne() => Seq(D(2), Sp, N, Sp, Minus, Sp, D(1));

    private static Formula CoefficientFormula()
    {
        Formula twoNPlusTwo = Seq(D(2), Sp, N, Sp, Plus, Sp, D(2));
        Formula affine = Paren(Seq(
            D(2), Sp, Pow(N, D(2)), Sp, Minus, Sp, D(1), Sp, Minus, Sp,
            Paren(TwoNMinusOne()), Sp, K));
        Formula summand = Seq(
            Pow(Paren(Seq(Minus, D(1))), K), Sp, Times, Sp,
            Call("binom", twoNPlusTwo, K), Sp, Times, Sp,
            Pow(affine, TwoNMinusOne()));
        Formula sum = Seq(
            new Formula.Subscript(Sum, Seq(D(0), Sp, Leq, Sp, K, Sp, Leq, Sp, N)),
            Sp, summand);
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, N, Sp, InMacro, Sp, Naturals, Comma),
            new Formula.Relation(Call("coefficient", N), FormulaRelationOperator.Equal, sum),
            Seq(Call("coefficient", N), Sp, InMacro, Sp, Integers, Dot),
        ]));
    }

    private static Formula ResultFormula() => Disp(new Formula.Aligned([
        Seq(Forall, Sp, N, Sp, InMacro, Sp, Naturals, Comma, Sp,
            AtMost(D(2), N), Sp, Implies),
        Seq(Call("coefficient", N), Sp, Lt, Sp, D(0), Dot),
    ]));

    private static Formula NormalizationFormula()
    {
        Formula scale = TwoNMinusOne();
        Formula exponent = TwoNMinusOne();
        Formula order = Seq(D(2), Sp, N, Sp, Plus, Sp, D(2));
        Formula point = new Formula.Fraction(
            Seq(D(2), Sp, Pow(N, D(2)), Sp, Minus, Sp, D(1)), scale);
        return In(new Formula.Relation(
            Call("real", Call("coefficient", N)),
            FormulaRelationOperator.Equal,
            Seq(Pow(Paren(scale), exponent), Sp, Times, Sp,
                Seq(Paren(scale), Bang), Sp, Times, Sp,
                Call("C", order, point))));
    }
}
