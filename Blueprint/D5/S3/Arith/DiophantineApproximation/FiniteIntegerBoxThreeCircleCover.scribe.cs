using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.DiophantineApproximation;

internal sealed class FiniteIntegerBoxThreeCircleCoverDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/Arith/DiophantineApproximation/FiniteIntegerBoxThreeCircleCover";
    private const string Transference =
        "D5/S3/Arith/Lattices/EuclideanThreeLatticeTransference.exists_dual_covering_four";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A missed strict phase window on a closed three-axis integer box forces a positive simultaneous resonance.",
        H("Finite three-axis integer-box inverse"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-integer-box-inverse-three"),
            DeclarationHandle.Create(Gid + ".finite_integer_box_inverse_three"),
            H("A padded joint squared resonance bound of 43/9"),
            StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Set Rᵢ = Nᵢ + 2. The triangular lattice has three coordinates bᵢ/Rᵢ "
                    + "and fourth coordinate (∑ᵢ bᵢθᵢ − m)/w. Use the center with axis coordinates "
                    + "3Nᵢ/(2Rᵢ) and fourth coordinate (t + w/2)/w. A point at distance less "
                    + "than 1/2 would give Nᵢ − 1 < bᵢ < 2Nᵢ + 1 on each axis. "
                    + "Integrality includes both endpoints Nᵢ and 2Nᵢ, and the fourth "
                    + "coordinate gives a strict phase hit.")),
                Paragraph(Text(
                    "The missed window therefore bounds the distance to each lattice point "
                    + "below by 1/2. At the center the four-dimensional covering bound gives "
                    + "a nonzero integral-dual vector of squared length at most 4·(43/36) = 43/9. "),
                    Ref(Transference)),
                Paragraph(Text(
                    "The dual coordinates are Rᵢ(jᵢ − hθᵢ) and wh. If h were zero, "
                    + "any nonzero jᵢ would give a squared coordinate at least Rᵢ² ≥ 9, "
                    + "which exceeds 43/9. Since the dual vector is nonzero, h is nonzero. "
                    + "Reversing the common sign if needed yields h ≥ 1 with the same norm."))),
            DescribeRole.Theorem))));

    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Integers => new Formula.Integers();
    private static Formula Axes => new Formula.Apply(Seq(Operatorname, Grp(F.Id("Fin"))), [D(3)]);
    private static Formula Parens(Formula value) => Seq(Open, value, Close);
    private static Formula Real(Formula value) => Parens(Seq(value, Sp, Colon, Sp, Reals));
    private static Formula At(Formula value, Formula index) => new Formula.Subscript(value, index);
    private static Formula Square(Formula value) => new Formula.Power(value, D(2));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula AxisSum(Formula index, Formula term) =>
        Seq(new Formula.Subscript(Sum, Seq(index, Sp, InMacro, Sp, Axes)), Sp, Parens(term));

    private static Formula Statement()
    {
        Formula n = F.Id("N"), t = F.Id("t"), w = F.Id("w"), i = F.Id("i");
        Formula b = F.Id("b"), m = F.Id("m"), h = F.Id("h"), j = F.Id("j");
        Formula integerAxes = Seq(Axes, Sp, To, Sp, Integers);
        Formula realAxes = Seq(Axes, Sp, To, Sp, Reals);
        Formula ni = At(n, i), bi = At(b, i), thetaI = At(Theta, i);
        Formula phase = Sub(AxisSum(i, Mul(Real(bi), thetaI)), Real(m));
        Formula axisError = Sub(Mul(Real(h), thetaI), Real(At(j, i)));
        Formula joint = Add(AxisSum(i, Mul(Square(Add(Real(ni), D(2))), Square(axisError))),
            Mul(Square(w), Square(Real(h))));

        return Seq(
            Forall, Sp, n, Colon, Sp, integerAxes, Comma, Sp,
            Parens(Seq(Forall, Sp, i, Colon, Sp, Axes, Comma, Sp, D(1), Sp, Le, Sp, ni)), Sp, To, Sp,
            Forall, Sp, Theta, Colon, Sp, realAxes, Comma, Sp,
            Forall, Sp, t, Comma, Sp, w, Colon, Sp, Reals, Comma, Sp,
            D(0), Sp, Lt, Sp, w, Sp, To, Sp,
            Neg, Sp, Parens(Seq(
                Exists, Sp, b, Colon, Sp, integerAxes, Comma, Sp,
                Exists, Sp, m, Colon, Sp, Integers, Comma, Sp,
                Parens(Seq(Forall, Sp, i, Colon, Sp, Axes, Comma, Sp,
                    ni, Sp, Le, Sp, bi, Sp, Land, Sp, bi, Sp, Le, Sp, Mul(D(2), ni))), Sp, Land, Sp,
                t, Sp, Lt, Sp, phase, Sp, Land, Sp, phase, Sp, Lt, Sp, Add(t, w))), Sp, To, Sp,
            Exists, Sp, h, Colon, Sp, Integers, Comma, Sp,
            Exists, Sp, j, Colon, Sp, integerAxes, Comma, Sp,
            D(1), Sp, Le, Sp, h, Sp, Land, Sp, joint, Sp, Le, Sp, new Formula.Fraction(D(4, 3), D(9)));
    }
}
