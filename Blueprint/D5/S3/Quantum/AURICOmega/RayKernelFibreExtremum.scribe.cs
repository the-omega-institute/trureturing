using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.AURICOmega;

internal sealed class RayKernelFibreExtremumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/AURICOmega/RayKernelFibreExtremum.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Along a right coset of the phase circle of the unit quaternions the round-trip reading and the squared shifted reading attain the ray kernel as their maximum, and the squared inner product has the ray kernel times pi as its integral over a full turn.",
        H("The phase circle of the unit quaternions and the fibre extremum of the reading"),
        Blocks(
            Node("phase-circle", "phaseCircle", "The phase circle",
                StatementSource.FromAuthor(PhaseCircleFormula()), AssessedProvenance.FromRepo(), DescribeRole.Definition,
                "phaseCircle is the subgroup of the unit quaternions whose elements have vanishing j and k components, that is the unit quaternions a + b i with a^2 + b^2 = 1. "
                    + "It is closed under products because the j and k components of a product of two elements of the real span of 1 and i vanish, and under inverses because the inverse of a unit quaternion is its conjugate. "
                    + "The quotient of the unit quaternions by this subgroup is formed with the cosets x * phaseCircle, so two unit quaternions lie in the same class exactly when they differ by a factor of the circle on the right. "
                    + "Remark (not stated as a theorem here): the Hopf map sends x to x * i * star x, and the ray kernel is a function of the inner product of Hopf images, equal to one exactly on the right cosets of the phase circle; together with the conjugacy of unit quaternions with equal real parts, these results show that the Hopf map induces a bijection from the quotient of the unit quaternions by the phase circle onto the sphere of unit imaginary quaternions, and this bijection is a homeomorphism because it is continuous, the quotient is compact and the sphere is Hausdorff."),
            Node("fibre-extremum", "rayKernel_isGreatest_and_integral", "Maximum and integral of the reading over a fibre",
                StatementSource.FromAuthor(ExtremumFormula()), AssessedProvenance.FromRepo(), DescribeRole.Theorem,
                "In the display, kappa and tri are the reading and the transfer of the quaternion comparison model, with kappa(x, y) = (1 + <x, y>) / 2 and tri(p, y, p) = p * y^-1 * p, IsGreatest(S, m) means that m belongs to S and bounds S from above, mk(a, b, c, d) is the quaternion a + b i + c j + d k, and the integration variable t runs over the interval from 0 to 2 pi. "
                    + "For all unit quaternions x and y the three conjuncts state: over the right phase circle of x, the round-trip reading kappa(y, (x c) y^-1 (x c)) has largest value rayKernel(x, y); the squared shifted reading (2 kappa(x c, y) - 1)^2 has the same largest value; and the integral over a full turn of the squared inner product of x (cos t + sin t i) with y equals pi times rayKernel(x, y). "
                    + "Put A = 2 kappa(x, y) - 1 and B = 2 kappa(x, y * i) - 1, so that rayKernel(x, y) = A^2 + B^2 by definition. For a phase c = a + b i one has 2 kappa(x c, y) - 1 = a A - b B, since right multiplication by a + b i mixes the inner products with y and with y * i. "
                    + "Over the circle a^2 + b^2 = 1 the square (a A - b B)^2 is at most A^2 + B^2 by the Cauchy-Schwarz inequality, with equality at a = A / r, b = -B / r for r the square root of A^2 + B^2, and at c = 1 when A = B = 0. "
                    + "For a unit quaternion p the round-trip identity kappa(y, p y^-1 p) = (2 kappa(p, y) - 1)^2 holds, because the real part of y^-1 p y^-1 p equals 2 <p, y>^2 - 1 for unit p and y; so the first set equals the second. "
                    + "Finally the squared inner product along the circle is A^2 cos^2 t + B^2 sin^2 t - 2 A B sin t cos t, whose integral over a full turn is pi (A^2 + B^2). "
                    + "Thus the ray kernel is both the fibre maximum of the round-trip reading and pi^-1 times the integral of the squared inner product over the fibre, that is twice its mean over a full turn."))));

    private static DocumentBlock Node(
        string id, string selector, string title, StatementSource statement,
        AssessedProvenance provenance, DescribeRole role, string prose) =>
        Describe.Lean(DescribeId.Create("quaternion-hopf-fibration-" + id),
            DeclarationHandle.Create(Prefix + selector), H(title), statement, provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Rel(Formula x, FormulaRelationOperator op, Formula y) => new Formula.Relation(x, op, y);
    private static Formula Equal(Formula x, Formula y) => Rel(x, FormulaRelationOperator.Equal, y);
    private static Formula Logic(Formula x, FormulaLogicOperator op, Formula y) => new Formula.Logic(x, op, y);
    private static Formula And(Formula x, Formula y) => Logic(x, FormulaLogicOperator.And, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Square(Formula x) => new Formula.Power(x, D(2));
    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula ForAllMany(Formula domain, Formula body, params string[] names) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [.. names.Select(name => new Formula.BoundVariable(FormulaIdentifier.Create(name), domain))], body);

    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Quaternions => Seq(Mathbb, Grp(F.Id("H")), OpenBracket, Reals, CloseBracket);
    private static Formula Units => Call("unitary", Quaternions);
    private static Formula PhaseCircle => Seq(Operatorname, Grp(F.Id("phaseCircle")));
    private static Formula Model => Seq(Operatorname, Grp(F.Id("quaternionModel")));
    private static Formula Kappa(Formula x, Formula y) => Call("kappa", Model, x, y);
    private static Formula Tri(Formula p, Formula y, Formula q) => Call("tri", Model, p, y, q);
    private static Formula RayKernel(Formula x, Formula y) => Call("rayKernel", x, y);
    private static Formula Inner(Formula x, Formula y) =>
        new Formula.Subscript(Seq(Langle, Sp, x, Comma, Sp, y, Sp, Rangle), Reals);
    private static Formula PhaseCircleFormula()
    {
        Formula c = F.Id("c");
        return Disp(ForAll("c", Units, Logic(Rel(c, FormulaRelationOperator.MemberOf, PhaseCircle),
            FormulaLogicOperator.Iff, And(Equal(Call("imJ", c), D(0)), Equal(Call("imK", c), D(0))))));
    }

    private static Formula ExtremumFormula()
    {
        Formula x = F.Id("x"), y = F.Id("y"), c = F.Id("c"), r = F.Id("r"), t = F.Id("t");
        Formula xc = Mul(x, c);
        Formula roundTrip = Seq(OpenBrace, r, Sp, Mid, Sp,
            Exists("c", PhaseCircle, Equal(r, Kappa(y, Tri(xc, y, xc)))), CloseBrace);
        Formula shifted = Seq(OpenBrace, r, Sp, Mid, Sp,
            Exists("c", PhaseCircle, Equal(r, Square(Sub(Mul(D(2), Kappa(xc, y)), D(1))))), CloseBrace);
        Formula turn = Call("mk", Call("cos", t), Call("sin", t), D(0), D(0));
        Formula integral = Seq(Int, Underscore, Grp(D(0)), Caret, Grp(D(2), Pi), Sp,
            Square(Inner(Mul(x, turn), y)), Sp, F.Id("d"), F.Id("t"));
        Formula first = Call("IsGreatest", roundTrip, RayKernel(x, y));
        Formula second = Call("IsGreatest", shifted, RayKernel(x, y));
        Formula third = Equal(integral, Mul(Seq(Pi), RayKernel(x, y)));
        return Disp(ForAllMany(Units, And(first, And(second, third)), "x", "y"));
    }
}
