using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.DiophantineApproximation;

internal sealed class AffineCongruenceIntegerBoxThreeCoverDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/Arith/DiophantineApproximation/AffineCongruenceIntegerBoxThreeCover";
    private const string BoxInverse =
        "D5/S3/Arith/DiophantineApproximation/FiniteIntegerBoxThreeCircleCover.finite_integer_box_inverse_three";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A missed strict phase window on a closed three-axis integer box forces a unique positive primitive label.",
        H("Affine congruence obstruction for a missed three-axis integer box"),
        Blocks(Describe.Lean(
            DescribeId.Create("short-label-miss-obstruction"),
            DeclarationHandle.Create(Gid + ".short_label_miss_obstruction"),
            H("The unique padded short label and its phase obstruction"),
            StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromRepo(),
            Blocks(
                LabelConditions(),
                PhaseData(),
                Paragraph(Text(
                    "The finite-box inverse supplies a positive joint resonance. Divide all four "
                    + "integer coordinates by their joint gcd. The joint squared length can only "
                    + "decrease, and the gcd identity gives Bézout's identity for the reduced label. "),
                    Ref(BoxInverse)),
                Paragraph(Text(
                    "For uniqueness, project two labels to the two coordinates Nᵢδᵢ and wh on "
                    + "each axis i. Each row has squared length at most 43/9, since the padded "
                    + "bound also bounds the unpadded rows. The area of the two rows is at most "
                    + "the product of their lengths, hence at most 43/9. That area is Nᵢw times "
                    + "the absolute value of the integer cross minor h p′ᵢ − h′ pᵢ. The strict "
                    + "side-width hypothesis forces each minor to vanish. The two Bézout "
                    + "identities then give mutual divisibility of the positive denominators "
                    + "and equality of the numerators.")),
                Paragraph(Text(
                    "The unpadded square estimate and the side-width hypotheses give 2h < Nᵢ "
                    + "on every axis and E < w. If an integer n lay strictly inside the phase band "
                    + "of radius R − hE, the continuous linear image of the inset box "
                    + "[Nᵢ + h/2, 2Nᵢ − h/2] would meet the phase interval after reserving hE/2 "
                    + "for rounding. For Bézout coefficients u and vᵢ, round each inset "
                    + "coordinate to the nearest integer bᵢ in the class n vᵢ modulo h. "
                    + "This preserves the original closed box and realizes ∑ᵢ bᵢpᵢ − ha = n "
                    + "for an integer a. Each coordinate moves by at most h/2, so the change "
                    + "in the linear image is at most hE/2 and the resulting phase hit is strict.")),
                Paragraph(Text(
                    "Apply the exclusion inequality to an integer nearest the phase. Its distance "
                    + "is at most 1/2, giving 2(R − hE) ≤ 1, the weighted width bound. The weights "
                    + "Nᵢ − 2h are positive, so dropping the error sum and dividing by w gives "
                    + "the reciprocal denominator bound."))),
            DescribeRole.Theorem))));

    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Integers => new Formula.Integers();
    private static Formula Axes => new Formula.Apply(Seq(Operatorname, Grp(F.Id("Fin"))), [D(3)]);
    private static Formula IntegerAxes => Seq(Axes, Sp, To, Sp, Integers);
    private static Formula RealAxes => Seq(Axes, Sp, To, Sp, Reals);
    private static Formula Parens(Formula value) => Seq(Open, value, Close);
    private static Formula Real(Formula value) => Parens(Seq(value, Sp, Colon, Sp, Reals));
    private static Formula At(Formula value, Formula index) => new Formula.Subscript(value, index);
    private static Formula Field(Formula label, Formula field) => Seq(label, Dot, field);
    private static Formula Error(Formula label, Formula index) => At(F.Id("x"), Seq(label, Comma, Sp, index));
    private static Formula Abs(Formula value) => new Formula.Absolute(value);
    private static Formula Square(Formula value) => new Formula.Power(value, D(2));
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula AxisSum(Formula index, Formula term) =>
        Seq(At(Sum, Seq(index, Sp, InMacro, Sp, Axes)), Sp, Parens(term));
    private static Formula LabelType(Formula n, Formula w) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id("ShortLabel"))), [n, Theta, w]);

    private static Formula Statement()
    {
        Formula n = F.Id("N"), t = F.Id("t"), w = F.Id("w"), i = F.Id("i");
        Formula b = F.Id("b"), a = F.Id("a"), integer = F.Id("n");
        Formula label = F.Id("L"), other = Seq(label, Apos);
        Formula denominator = Real(Field(label, F.Id("h")));
        Formula ni = At(n, i), bi = At(b, i);
        Formula hit = Sub(AxisSum(i, Mul(Real(bi), At(Theta, i))), Real(a));
        Formula width = Add(Mul(denominator, w),
            AxisSum(i, Mul(Sub(Real(ni), Mul(D(2), denominator)), Abs(Error(label, i)))));
        Formula labelType = LabelType(n, w);

        return Seq(
            Forall, Sp, n, Colon, Sp, IntegerAxes, Comma, Sp,
            Forall, Sp, Theta, Colon, Sp, RealAxes, Comma, Sp,
            Forall, Sp, t, Comma, Sp, w, Colon, Sp, Reals, Comma, Sp,
            D(0), Sp, Lt, Sp, w, Sp, To, Sp,
            Parens(Seq(Forall, Sp, i, Colon, Sp, Axes, Comma, Sp,
                Div(D(4, 3), D(9)), Sp, Lt, Sp, Mul(Real(ni), w))), Sp, To, Sp,
            Neg, Sp, Parens(Seq(
                Exists, Sp, b, Colon, Sp, IntegerAxes, Comma, Sp,
                Exists, Sp, a, Colon, Sp, Integers, Comma, Sp,
                Parens(Seq(Forall, Sp, i, Colon, Sp, Axes, Comma, Sp,
                    ni, Sp, Le, Sp, bi, Sp, Land, Sp, bi, Sp, Le, Sp, Mul(D(2), ni))), Sp, Land, Sp,
                t, Sp, Lt, Sp, hit, Sp, Land, Sp, hit, Sp, Lt, Sp, Add(t, w))), Sp, To, Sp,
            Exists, Sp, label, Colon, Sp, labelType, Comma, Sp,
            Parens(Seq(Forall, Sp, other, Colon, Sp, labelType, Comma, Sp, other, Sp, Eq, Sp, label)), Sp, Land, Sp,
            Parens(Seq(Forall, Sp, integer, Colon, Sp, Integers, Comma, Sp,
                Sub(At(F.Id("R"), label), Mul(denominator, At(F.Id("E"), label))), Sp, Le, Sp,
                Abs(Sub(Real(integer), At(Xi, label))))), Sp, Land, Sp,
            Parens(Seq(width, Sp, Le, Sp, D(1))), Sp, Land, Sp,
            Parens(Seq(denominator, Sp, Le, Sp, Div(D(1), w))));
    }

    private static DocumentBlock LabelConditions()
    {
        Formula n = F.Id("N"), w = F.Id("w"), label = F.Id("L");
        Formula i = F.Id("i"), u = F.Id("u"), v = F.Id("v");
        Formula h = Field(label, F.Id("h")), p = Field(label, F.Id("p"));
        Formula bezout = Add(Mul(h, u), AxisSum(i, Mul(At(p, i), At(v, i))));
        Formula joint = Add(
            AxisSum(i, Square(Mul(Add(Real(At(n, i)), D(2)), Error(label, i)))),
            Square(Mul(w, Real(h))));

        return Paragraph(
            Math(LabelType(n, w)), Text(" consists of an integer denominator "),
            Math(Seq(h, Sp, InMacro, Sp, Integers)), Text(" with "),
            Math(Seq(D(1), Sp, Le, Sp, h)), Text(" and an integer numerator function "),
            Math(Seq(p, Colon, Sp, IntegerAxes)), Text(". Joint primitiveness means "),
            Math(Seq(Exists, Sp, u, Colon, Sp, Integers, Comma, Sp,
                Exists, Sp, v, Colon, Sp, IntegerAxes, Comma, Sp, bezout, Sp, Eq, Sp, D(1))),
            Text(". The padded joint square bound is "),
            Math(Seq(joint, Sp, Le, Sp, Div(D(4, 3), D(9)))), Text("."));
    }

    private static DocumentBlock PhaseData()
    {
        Formula n = F.Id("N"), t = F.Id("t"), w = F.Id("w"), label = F.Id("L"), i = F.Id("i");
        Formula denominator = Real(Field(label, F.Id("h")));
        Formula x = Error(label, i), ni = Real(At(n, i));
        Formula error = Sub(Mul(denominator, At(Theta, i)), Real(At(Field(label, F.Id("p")), i)));
        Formula phase = Sub(Mul(denominator, Add(t, Div(w, D(2)))),
            AxisSum(i, Mul(Div(Mul(D(3), ni), D(2)), x)));
        Formula radius = Div(Add(Mul(denominator, w), AxisSum(i, Mul(ni, Abs(x)))), D(2));

        return Paragraph(
            Text("For each axis the signed error is "), Math(Seq(x, Sp, Eq, Sp, error)),
            Text(". The phase and radius use the original side lengths "),
            Math(At(n, i)), Text(". The phase is "), Math(Seq(At(Xi, label), Sp, Eq, Sp, phase)),
            Text(", the radius is "), Math(Seq(At(F.Id("R"), label), Sp, Eq, Sp, radius)),
            Text(", and the error sum is "), Math(Seq(At(F.Id("E"), label), Sp, Eq, Sp, AxisSum(i, Abs(x)))),
            Text("."));
    }
}
