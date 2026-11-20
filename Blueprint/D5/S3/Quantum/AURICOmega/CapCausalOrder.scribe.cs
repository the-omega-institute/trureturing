using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.AURICOmega;

internal sealed class CapCausalOrderDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/AURICOmega/CapCausalOrder.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Open caps of the unit quaternions with angular radius in (0, pi) correspond bijectively to the points of the one-sheeted hyperboloid |v|^2 - t^2 = 1 in R x H, a cap determines its centre and radius, and inclusion of caps is the causal order of the corresponding points.",
        H("Caps of the unit quaternions and the causal order of the hyperboloid"),
        Blocks(
            Node("cap", "cap", "The open cap with centre n and angular radius a",
                StatementSource.FromAuthor(CapFormula()), DescribeRole.Definition,
                "For a unit quaternion n and a real number a, the cap cap(n, a) is the set of unit quaternions x whose reading with n in the quaternion comparison model exceeds cos(a/2)^2. "
                    + "The reading is kappa(quaternionModel, n, x) = (1 + <n, x>) / 2 for the real inner product <n, x> of quaternions, and cos(a/2)^2 = (1 + cos(a)) / 2, so x lies in cap(n, a) exactly when cos(a) < <n, x>. "
                    + "For a in (0, pi) this is the open spherical cap of the unit three-sphere with centre n and angular radius a: the unit quaternions whose angle with n is less than a. "
                    + "The definition is made for every real a and depends on a only through cos(a). At the endpoint radii, a = pi gives the complement of the single point -n, because <n, x> > -1 fails only for x = -n, and a = 0 gives the empty set, because <n, x> <= 1 for unit quaternions."),
            Node("de-sitter-point", "deSitterPoint", "The hyperboloid point of a cap",
                StatementSource.FromAuthor(PointFormula()), DescribeRole.Definition,
                "To a unit quaternion n and a real number a the definition attaches the pair (-cos(a)/sin(a), sin(a)^-1 n) of R x H, where n is viewed as a quaternion and sin(a)^-1 n is its real scalar multiple. "
                    + "For a in (0, pi) one has sin(a) > 0, and the identity sin(a)^-2 - cos(a)^2 / sin(a)^2 = 1 shows that the pair lies on the hyperboloid |v|^2 - t^2 = 1. "
                    + "Its first coordinate -cot(a) increases strictly with a on (0, pi), and its second coordinate points in the direction of the centre n. "
                    + "The theorem below uses the definition only for a in (0, pi)."),
            Node("cap-causal-order", "cap_causal_order", "Caps, hyperboloid points and the causal order",
                StatementSource.FromAuthor(TheoremFormula()), DescribeRole.Theorem,
                "In the formula the pair (n', a') is written (m, b), a centre and radius pair is written p with coordinates fst(p) and snd(p), and a point of R x H is written w. "
                    + "The theorem has three parts. First, the map sending a centre and a radius (n, a) to deSitterPoint(n, a) is a bijection from the pairs with a in (0, pi) onto the hyperboloid {(t, v) in R x H : |v|^2 - t^2 = 1}. "
                    + "Second, for radii a and a' in (0, pi), cap(n, a) = cap(n', a') holds exactly when n = n' and a = a'. "
                    + "Third, for radii a and a' in (0, pi), cap(n, a) is contained in cap(n', a') exactly when, writing (t, v) = deSitterPoint(n, a) and (t', v') = deSitterPoint(n', a'), one has t <= t' and |v' - v|^2 <= (t' - t)^2, that is, when the difference (t' - t, v' - v) lies in the closed future cone of the quadratic form t^2 - |v|^2 on R x H. "
                    + "The inverse of the point map sends (t, v) on the hyperboloid to the centre v / |v| and the radius arccos(-t / |v|); the hyperboloid equation forces |v| > 0 and (-t / |v|)^2 = 1 - |v|^-2 < 1, so the radius lies in (0, pi) and sin of the radius is |v|^-1. "
                    + "The second and third parts rest on one inclusion criterion: for a and a' in (0, pi), cap(n, a) is contained in cap(n', a') exactly when a <= a' and cos(a' - a) <= <n, n'>, equivalently when the angle between n and n' plus a is at most a'. "
                    + "If this holds, the triangle inequality for angles between unit vectors places every point of cap(n, a) at angle less than a' from n'. "
                    + "If it fails, choose a unit quaternion u orthogonal to n whose inner product with n' is minus the length of the component of n' orthogonal to n, and choose an angle b with 0 <= b < a, a' <= phi + b and phi + b <= pi, where phi is the angle between n and n'. "
                    + "The point x = cos(b) n + sin(b) u is a unit quaternion with <n, x> = cos(b) > cos(a), so x lies in cap(n, a), while <n', x> = cos(phi + b) <= cos(a'), so x does not lie in cap(n', a'). "
                    + "Equal caps contain each other, so the criterion gives a = a' and <n, n'> >= 1, which forces n = n' for unit quaternions. "
                    + "For the third part, -cot(a) <= -cot(a') holds exactly when a <= a', because cos(a') sin(a) - cos(a) sin(a') = sin(a - a'). "
                    + "Expanding both sides with |n| = |n'| = 1 and cot(a)^2 = sin(a)^-2 - 1 gives |v' - v|^2 = sin(a')^-2 + sin(a)^-2 - 2 <n, n'> / (sin(a) sin(a')) and (t' - t)^2 = sin(a')^-2 + sin(a)^-2 - 2 cos(a' - a) / (sin(a) sin(a')), so the second inequality is equivalent to cos(a' - a) <= <n, n'>. "
                    + "The restriction of the radii to (0, pi) cannot be dropped. The caps with a = pi, the complement of the point -n, and with a = 0, the empty set, do not correspond to points of the hyperboloid, since sin(a) = 0 there; and all caps of radius 0 coincide, so caps of radius 0 do not determine their centre. "
                    + "The statement concerns the hyperboloid as a subset of R x H and the displayed coordinate inequality between its points. A metric on the hyperboloid, its identification with de Sitter space and any physical reading of the causal condition are not part of the statement. "
                    + "The correspondence between oriented spheres of a sphere and the points of the one-sheeted hyperboloid, with inclusion of caps as the causal order, is classical in Möbius geometry; see for instance U. Hertrich-Jeromin, Introduction to Möbius Differential Geometry. "
                    + "Here the caps are defined through the reading of the quaternion comparison model on the unit quaternions."))));

    private static DocumentBlock Node(
        string id, string selector, string title, StatementSource statement, DescribeRole role, string prose) =>
        Describe.Lean(DescribeId.Create("cap-causal-order-" + id),
            DeclarationHandle.Create(Prefix + selector), H(title), statement, AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Rel(Formula x, FormulaRelationOperator op, Formula y) => new Formula.Relation(x, op, y);
    private static Formula Lt(Formula x, Formula y) => Rel(x, FormulaRelationOperator.LessThan, y);
    private static Formula Le(Formula x, Formula y) => Rel(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Eq(Formula x, Formula y) => Rel(x, FormulaRelationOperator.Equal, y);
    private static Formula Mem(Formula x, Formula y) => Rel(x, FormulaRelationOperator.MemberOf, y);
    private static Formula Sub(Formula x, Formula y) => Rel(x, FormulaRelationOperator.SubsetOf, y);
    private static Formula Logic(Formula x, FormulaLogicOperator op, Formula y) => new Formula.Logic(x, op, y);
    private static Formula And(Formula x, Formula y) => Logic(x, FormulaLogicOperator.And, y);
    private static Formula Implies(Formula x, Formula y) => Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Iff(Formula x, Formula y) => Logic(x, FormulaLogicOperator.Iff, y);
    private static Formula Diff(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Sq(Formula x) => new Formula.Power(x, D(2));
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula AllMany(Formula domain, Formula body, params string[] names) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [.. names.Select(name => new Formula.BoundVariable(FormulaIdentifier.Create(name), domain))], body);

    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Quaternions => Seq(Mathbb, Grp(F.Id("H")), OpenBracket, Reals, CloseBracket);
    private static Formula Units => Call("unitary", Quaternions);
    private static Formula Model => Seq(Operatorname, Grp(F.Id("quaternionModel")));
    private static Formula Radii => Call("Ioo", D(0), Pi);

    /// <summary>The set { x in domain | condition }.</summary>
    private static Formula SetOf(string x, Formula domain, Formula condition) =>
        Seq(OpenBrace, Sp, F.Id(x), Sp, InMacro, Sp, domain, Sp, Mid, Sp, condition, Sp, CloseBrace);

    private static Formula Pair(Formula x, Formula y) => Seq(Open, x, Comma, Sp, y, Close);

    private static Formula CapFormula()
    {
        Formula n = F.Id("n"), a = F.Id("a"), x = F.Id("x");
        Formula condition = Lt(Sq(Call("cos", new Formula.Fraction(a, D(2)))), Call("kappa", Model, n, x));
        return Disp(All("n", Units, All("a", Reals,
            Eq(Call("cap", n, a), SetOf("x", Units, condition)))));
    }

    private static Formula PointFormula()
    {
        Formula n = F.Id("n"), a = F.Id("a");
        Formula time = new Formula.Negate(new Formula.Fraction(Call("cos", a), Call("sin", a)));
        Formula space = Seq(new Formula.Power(Call("sin", a), Seq(F.Minus, D(1))), Sp, Cdot, Sp, n);
        return Disp(All("n", Units, All("a", Reals, Eq(Call("deSitterPoint", n, a), Pair(time, space)))));
    }

    private static Formula Point(Formula n, Formula a) => Call("deSitterPoint", n, a);
    private static Formula Fst(Formula x) => Call("fst", x);
    private static Formula Snd(Formula x) => Call("snd", x);

    private static Formula TheoremFormula()
    {
        Formula p = F.Id("p"), w = F.Id("w"), n = F.Id("n"), m = F.Id("m"), a = F.Id("a"), b = F.Id("b");
        Formula pointMap = Seq(p, Sp, Mapsto, Sp, Point(Fst(p), Snd(p)));
        Formula domain = SetOf("p", Seq(Units, Sp, F.Times, Sp, Reals), Mem(Snd(p), Radii));
        Formula hyperboloid = SetOf("w", Seq(Reals, Sp, F.Times, Sp, Quaternions),
            Eq(Diff(Sq(new Formula.Norm(Snd(w))), Sq(Fst(w))), D(1)));
        Formula bijection = Call("BijOn", pointMap, domain, hyperboloid);

        Formula equalCaps = Iff(Eq(Call("cap", n, a), Call("cap", m, b)), And(Eq(n, m), Eq(a, b)));
        Formula causal = And(
            Le(Fst(Point(n, a)), Fst(Point(m, b))),
            Le(Sq(new Formula.Norm(Diff(Snd(Point(m, b)), Snd(Point(n, a))))),
                Sq(Diff(Fst(Point(m, b)), Fst(Point(n, a))))));
        Formula inclusion = Iff(Sub(Call("cap", n, a), Call("cap", m, b)), causal);

        Formula Guarded(Formula body) => AllMany(Units, AllMany(Reals,
            Implies(Mem(a, Radii), Implies(Mem(b, Radii), body)), "a", "b"), "n", "m");

        return Disp(And(bijection, And(Guarded(equalCaps), Guarded(inclusion))));
    }
}
