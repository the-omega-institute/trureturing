using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class SincSquareChordSlopeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Dynamics/SincSquareChordSlope.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Let psi(x) = (sin x / x)^2. For a base point theta in (0, pi/2], the chord slope (psi(theta) - psi(u)) / (u^2 - theta^2) of psi in the squared variable is strictly decreasing in u on (theta, infinity): for theta < u < v, (psi(theta) - psi(v)) (u^2 - theta^2) < (psi(theta) - psi(u)) (v^2 - theta^2).",
        H("The chord slope of the squared sinc function in the squared variable"),
        Blocks(
            Node("chord", "Chord slopes from a base point in (0, pi/2] strictly decrease", ChordFormula(),
                "Write psi(x) = (sin x / x)^2 and Gamma(u) = (psi(theta) - psi(u)) / (u^2 - theta^2) for u > theta; the statement is Gamma(v) < Gamma(u) with the denominators cleared. The derivative is Gamma'(u) = -2u T(theta, u) / (u^2 - theta^2)^2 with the tangent expression T(theta, u) = psi(theta) - psi(u) + q(u) (u^2 - theta^2) / 2, where q(u) = psi'(u) / u = (u sin 2u - 1 + cos 2u) / u^4, so it suffices to prove T(theta, u) > 0 for 0 < theta < u and theta <= pi/2. First, q is strictly increasing on (0, pi]: q'(u) = n(2u) / u^5 with n(z) = (z^2/2) cos z - (5z/2) sin z + 4 - 4 cos z, and n > 0 on (0, 2 pi]. On (0, pi] this follows from n(0) = n'(0) = 0 and n''(z) = (z/2)(sin z - z cos z) > 0, the last because sin z - z cos z vanishes at 0 and has derivative z sin z > 0. On (pi, 2 pi] write z = pi + w with 0 < w <= pi, so that n = 4 + (4 - z^2/2) cos w + (5z/2) sin w with z^2/2 > 4 and sin w >= 0: if w > pi/2 then cos w <= 0 and n >= 4; if w <= pi/2 then cos w <= 1 and Jordan's inequality sin w >= 2w/pi give n >= 8 - (pi + w)^2/2 + 5w >= 8 - pi^2/2 + (5 - 5 pi/4) w > 0 because pi < 4. Second, for u <= pi the function f(s) = T(s, u) on (0, u] has f(u) = 0 and f'(s) = s (q(s) - q(u)) < 0 for s < u, so T(theta, u) > 0; this case does not use theta <= pi/2. Third, for u > pi one has psi(u) <= 1/u^2 and -q(u) (u^2 - theta^2) / 2 = (1 - cos 2u - u sin 2u)(u^2 - theta^2) / (2u^4) <= (2 + u) / (2u^2), hence psi(u) - q(u) (u^2 - theta^2) / 2 <= (4 + u) / (2u^2) < 4 / pi^2, the last step because 8u^2 - (4 + u) pi^2 = 4 (u - pi)(u + pi) + u (4u - pi^2) > 0 for u > pi and pi < 4; and psi(theta) >= 4 / pi^2 for theta in (0, pi/2] by Jordan's inequality. The inequality is the analytic input for the positivity of the first-site amplitude of seven-site spin chains whose smallest positive eigenvalue divides the others, a question raised by the conjecture of Section 4 of Escobar, Garcia and Minenkova, arXiv:2507.18767; that paper is the motivation and not a source of the inequality.",
                "sincSq_chord_lt", DescribeRole.Theorem, AssessedProvenance.FromRepo())),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(
            DescribeId.Create("sincsq-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula LessEq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Minus2(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula AllReal(Formula variable, Formula body) =>
        Seq(Forall, Sp, variable, Sp, InMacro, Sp, Reals(), Comma, Sp, body);
    private static Formula Sq(Formula value) => new Formula.Power(value, D(2));
    private static Formula SincSq(Formula value) =>
        Sq(Parenthesized(new Formula.Fraction(Call("sin", value), value)));

    private static Formula ChordFormula()
    {
        Formula theta = Theta, u = F.Id("u"), v = F.Id("v");
        Formula hypotheses = Seq(
            Less(D(0), theta), Sp, Land, Sp,
            LessEq(theta, new Formula.Fraction(Pi, D(2))), Sp, Land, Sp,
            Less(theta, u), Sp, Land, Sp,
            Less(u, v));
        Formula left = Mul(Minus2(SincSq(theta), SincSq(v)), Minus2(Sq(u), Sq(theta)));
        Formula right = Mul(Minus2(SincSq(theta), SincSq(u)), Minus2(Sq(v), Sq(theta)));
        return Disp(AllReal(theta, AllReal(u, AllReal(v, Implies(hypotheses, Less(left, right))))));
    }
}
