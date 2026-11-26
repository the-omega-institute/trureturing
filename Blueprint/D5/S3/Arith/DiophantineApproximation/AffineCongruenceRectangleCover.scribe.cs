using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.DiophantineApproximation;

internal sealed class AffineCongruenceRectangleCoverDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/Arith/DiophantineApproximation/AffineCongruenceRectangleCover";
    private const string RectangleInverse =
        "D5/S3/Arith/DiophantineApproximation/FiniteRectangleCircleCover.finite_rectangle_inverse";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A missed affine rectangle forces a unique primitive label and a phase obstruction.",
        H("Affine congruence obstruction for a missed rectangle"),
        Blocks(Describe.Lean(
            DescribeId.Create("short-label-miss-obstruction"),
            DeclarationHandle.Create(Gid + ".short_label_miss_obstruction"),
            H("The unique short label and its weighted phase obstruction"),
            StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromRepo(),
            Blocks(
                LabelConditions(),
                PhaseData(),
                Paragraph(Text(
                    "The rectangle includes its integer endpoints and the phase window has strict endpoints. "
                    + "The side-width lower bounds keep both rounding margins positive and force the integer "
                    + "cross minors between any two short labels to vanish.")),
                Paragraph(Text(
                    "Divide the joint inverse label by its joint gcd to obtain a positive primitive label. "
                    + "Bézout supplies a residue pair for any integer in the inner phase band. A continuous "
                    + "box image and nearest-residue rounding would realize that integer in the target window. "
                    + "Since the window is missed, the phase inequality holds for every integer. Applying it "
                    + "at an integer nearest the phase gives the weighted width bound, whose nonnegative "
                    + "error terms then give the denominator bound. "), Ref(RectangleInverse))),
            DescribeRole.Theorem))));

    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers => new Formula.Integers();
    private static Formula Parens(Formula value) => Seq(Open, value, Close);
    private static Formula Cast(Formula value, Formula domain) => Parens(Seq(value, Sp, Colon, Sp, domain));
    private static Formula Real(Formula value) => Cast(value, Reals);
    private static Formula Abs(Formula value) => new Formula.Absolute(value);
    private static Formula Square(Formula value) => new Formula.Power(value, D(2));
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Field(Formula label, Formula field) => Seq(label, Dot, field);
    private static Formula Numerator(byte index) => new Formula.Subscript(F.Id("p"), D(index));
    private static Formula AtLabel(Formula value) => new Formula.Subscript(value, F.Id("L"));
    private static Formula LabelType(Formula n, Formula m, Formula w) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id("ShortLabel"))), [n, m, Theta, Phi, w]);
    private static Formula GcdOf(Formula a, Formula b) => new Formula.Apply(Gcd, [a, b]);

    private static Formula Statement()
    {
        Formula n = F.Id("N"), m = F.Id("M"), t = F.Id("t"), w = F.Id("w");
        Formula a = F.Id("a"), b = F.Id("b"), d = F.Id("d");
        Formula label = F.Id("L"), other = Seq(label, Apos), integer = F.Id("n");
        Formula denominator = Real(Field(label, F.Id("h")));
        Formula labelType = LabelType(n, m, w);
        Formula hit = Sub(Add(Mul(Real(b), Theta), Mul(Real(d), Phi)), Real(a));
        Formula width = Add(
            Add(Mul(denominator, w), Mul(Sub(Real(n), Mul(D(2), denominator)), Abs(AtLabel(F.Id("x"))))),
            Mul(Sub(Real(m), Mul(D(2), denominator)), Abs(AtLabel(F.Id("z")))));

        return Seq(
            Forall, Sp, n, Comma, Sp, m, Colon, Sp, Naturals, Comma, Sp,
            Forall, Sp, Theta, Comma, Sp, Phi, Comma, Sp, t, Comma, Sp, w, Colon, Sp, Reals, Comma, Sp,
            Parens(Seq(D(0), Sp, Lt, Sp, w, Sp, Land, Sp, w, Sp, Lt, Sp, D(1))), Sp, To, Sp,
            D(4), Sp, Le, Sp, Mul(Real(n), w), Sp, To, Sp, D(4), Sp, Le, Sp, Mul(Real(m), w), Sp, To, Sp,
            Neg, Sp, Parens(Seq(
                Exists, Sp, a, Colon, Sp, Integers, Comma, Sp, Exists, Sp, b, Comma, Sp, d, Colon, Sp, Naturals,
                Comma, Sp, n, Sp, Le, Sp, b, Sp, Land, Sp, b, Sp, Le, Sp, Mul(D(2), n), Sp, Land, Sp,
                m, Sp, Le, Sp, d, Sp, Land, Sp, d, Sp, Le, Sp, Mul(D(2), m), Sp, Land, Sp,
                t, Sp, Lt, Sp, hit, Sp, Land, Sp, hit, Sp, Lt, Sp, Add(t, w))), Sp, To, Sp,
            Exists, Sp, label, Colon, Sp, labelType, Comma, Sp,
            Parens(Seq(Forall, Sp, other, Colon, Sp, labelType, Comma, Sp, other, Sp, Eq, Sp, label)),
            Sp, Land, Sp,
            Parens(Seq(Forall, Sp, integer, Colon, Sp, Integers, Comma, Sp,
                Sub(AtLabel(F.Id("R")), Mul(denominator, AtLabel(F.Id("E")))), Sp, Le, Sp,
                Abs(Sub(Real(integer), AtLabel(Xi))))), Sp, Land, Sp,
            Parens(Seq(width, Sp, Le, Sp, D(1))), Sp, Land, Sp,
            Parens(Seq(denominator, Sp, Le, Sp, Div(D(1), w))));
    }

    private static DocumentBlock LabelConditions()
    {
        Formula n = F.Id("N"), m = F.Id("M"), w = F.Id("w"), label = F.Id("L");
        Formula h = Field(label, F.Id("h"));
        Formula p3 = Field(label, Numerator(3)), p5 = Field(label, Numerator(5));
        Formula primitive = GcdOf(Cast(h, Integers), Cast(GcdOf(p3, p5), Integers));
        Formula joint = Add(
            Add(Square(Mul(Real(n), AtLabel(F.Id("x")))), Square(Mul(Real(m), AtLabel(F.Id("z"))))),
            Square(Mul(w, Real(h))));

        return Paragraph(
            Math(LabelType(n, m, w)), Text(" contains a natural denominator "),
            Math(h), Text(" and signed integer numerators "), Math(p3), Text(" and "), Math(p5),
            Text(" with "), Math(Seq(D(1), Sp, Le, Sp, h)),
            Text(", joint primitiveness "), Math(Seq(primitive, Sp, Eq, Sp, D(1))),
            Text(", and the joint square bound "), Math(Seq(joint, Sp, Le, Sp, Div(D(1, 1), D(3)))),
            Text("."));
    }

    private static DocumentBlock PhaseData()
    {
        Formula n = F.Id("N"), m = F.Id("M"), t = F.Id("t"), w = F.Id("w"), label = F.Id("L");
        Formula denominator = Real(Field(label, F.Id("h")));
        Formula x = AtLabel(F.Id("x")), z = AtLabel(F.Id("z"));
        Formula phase = Sub(
            Sub(Mul(denominator, Add(t, Div(w, D(2)))), Mul(Div(Mul(D(3), Real(n)), D(2)), x)),
            Mul(Div(Mul(D(3), Real(m)), D(2)), z));
        Formula radius = Div(Add(Add(Mul(denominator, w), Mul(Real(n), Abs(x))), Mul(Real(m), Abs(z))), D(2));

        return Paragraph(
            Text("The signed errors are "),
            Math(Seq(x, Sp, Eq, Sp, Sub(Mul(denominator, Theta), Real(Field(label, Numerator(3)))))),
            Text(" and "),
            Math(Seq(z, Sp, Eq, Sp, Sub(Mul(denominator, Phi), Real(Field(label, Numerator(5)))))),
            Text(". The phase is "), Math(Seq(AtLabel(Xi), Sp, Eq, Sp, phase)),
            Text(", the radius is "), Math(Seq(AtLabel(F.Id("R")), Sp, Eq, Sp, radius)),
            Text(", and the absolute error sum is "), Math(Seq(AtLabel(F.Id("E")), Sp, Eq, Sp, Add(Abs(x), Abs(z)))),
            Text("."));
    }
}
