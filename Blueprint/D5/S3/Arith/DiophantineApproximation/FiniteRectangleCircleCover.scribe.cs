using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.DiophantineApproximation;

internal sealed class FiniteRectangleCircleCoverDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/Arith/DiophantineApproximation/FiniteRectangleCircleCover";
    private const string Transference =
        "D5/S3/Arith/Lattices/EuclideanThreeLatticeTransference.exists_dual_covering";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A missed open phase window on a closed integer rectangle forces a positive simultaneous resonance.",
        H("Finite rectangular circle-cover inverse"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-rectangle-circle-cover-inverse"),
            DeclarationHandle.Create(Gid + ".finite_rectangle_inverse"),
            H("A joint squared resonance bound of eleven thirds"),
            StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The rectangular constraints include their integer endpoints. The phase "
                    + "window is open, and the phases may be rational. Each natural or integer "
                    + "variable in a real expression is explicitly cast to ℝ in the formula.")),
                Paragraph(Text(
                    "The lattice points are (b/N, d/M, (bθ + dφ − a)/w) for integers b, d, a. "
                    + "A point at Euclidean distance less than 1/2 from (3/2, 3/2, (t + w/2)/w) "
                    + "would hit the rectangle and window. The covering bound at this center gives "
                    + "a squared dual length at most 4·(11/12) = 11/3. "), Ref(Transference)),
                Paragraph(Text(
                    "The dual coordinates are (N(j − hθ), M(k − hφ), wh) with integer h, j, k. "
                    + "Because N and M are at least 2 and 11/3 < 4, h = 0 would force j = k = 0. "
                    + "Changing the signs of all three integers when h is negative gives h ≥ 1 "
                    + "and preserves the joint bound.")),
                Paragraph(Text(
                    "The triangular-lattice reduction and joint constant are also derived in "
                    + "Pro receipt e5e86a56-5405-4540-a08f-501fa628496f."))),
            DescribeRole.Theorem))));

    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Cast(Formula value) => Seq(Open, value, Sp, Colon, Sp, Reals, Close);
    private static Formula Square(Formula value) => new Formula.Power(value, D(2));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);

    private static Formula Statement()
    {
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula integers = new Formula.Integers();
        Formula n = F.Id("N"), m = F.Id("M"), t = F.Id("t"), w = F.Id("w");
        Formula b = F.Id("b"), d = F.Id("d"), a = F.Id("a");
        Formula h = F.Id("h"), j = F.Id("j"), k = F.Id("k");
        Formula phase = Sub(Add(Mul(Cast(b), Theta), Mul(Cast(d), Phi)), Cast(a));
        Formula joint = Add(
            Add(Mul(Square(Cast(n)), Square(Sub(Mul(Cast(h), Theta), Cast(j)))),
                Mul(Square(Cast(m)), Square(Sub(Mul(Cast(h), Phi), Cast(k))))),
            Mul(Square(w), Square(Cast(h))));

        return Seq(
            Forall, Sp, n, Comma, Sp, m, Colon, Sp, naturals, Comma, Sp,
            D(2), Sp, Le, Sp, n, Sp, To, Sp, D(2), Sp, Le, Sp, m, Sp, To, Sp,
            Forall, Sp, Theta, Comma, Sp, Phi, Comma, Sp, t, Comma, Sp, w, Colon, Sp, Reals, Comma, Sp,
            Open, D(0), Sp, Lt, Sp, w, Sp, Land, Sp, w, Sp, Lt, Sp, D(1), Close, Sp, To, Sp,
            Neg, Sp, Open, Exists, Sp, b, Comma, Sp, d, Colon, Sp, naturals, Comma, Sp,
            Exists, Sp, a, Colon, Sp, integers, Comma, Sp,
            n, Sp, Le, Sp, b, Sp, Land, Sp, b, Sp, Le, Sp, Mul(D(2), n), Sp, Land, Sp,
            m, Sp, Le, Sp, d, Sp, Land, Sp, d, Sp, Le, Sp, Mul(D(2), m), Sp, Land, Sp,
            t, Sp, Lt, Sp, phase, Sp, Land, Sp, phase, Sp, Lt, Sp, Add(t, w), Close, Sp, To, Sp,
            Exists, Sp, h, Comma, Sp, j, Comma, Sp, k, Colon, Sp, integers, Comma, Sp,
            D(1), Sp, Le, Sp, h, Sp, Land, Sp, joint, Sp, Le, Sp,
            new Formula.Fraction(D(1, 1), D(3)));
    }
}
