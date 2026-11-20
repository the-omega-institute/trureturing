using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.AURICOmega;

internal sealed class QuaternionHopfFibrationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/AURICOmega/QuaternionHopfFibration.";
    private static LibraryNoteRef Hopf => LibraryNoteRef.Create("D5/L/Topology/hopf1931abbildungen");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Hopf map sends the unit quaternions onto the unit imaginary quaternions and identifies their quotient by the phase circle with that two-sphere; along a phase circle the squared shifted reading attains the ray kernel as its maximum and has the ray kernel times pi as its integral over a full turn.",
        H("The Hopf fibration of the unit quaternions and the fibre extremum of the reading"),
        Blocks(
            Node("phase-circle", "phaseCircle", "The phase circle",
                StatementSource.FromAuthor(PhaseCircleFormula()), AssessedProvenance.FromRepo(), DescribeRole.Definition,
                "phaseCircle is the subgroup of the unit quaternions whose elements have vanishing j and k components, that is the unit quaternions a + b i with a^2 + b^2 = 1. "
                    + "It is closed under products because the j and k components of a product of two elements of the real span of 1 and i vanish, and under inverses because the inverse of a unit quaternion is its conjugate. "
                    + "The quotient of the unit quaternions by this subgroup is formed with the cosets x * phaseCircle, so two unit quaternions lie in the same class exactly when they differ by a factor of the circle on the right."),
            Node("range-hopf", "range_hopf", "The range of the Hopf map",
                StatementSource.FromAuthor(RangeFormula()), AssessedProvenance.FromRepo(Hopf), DescribeRole.Theorem,
                "The Hopf map sends a unit quaternion x to hopf x = x * i * star x. "
                    + "The statement is that its range is exactly the set of quaternions n with real part re(n) = 0 and norm one. "
                    + "The image lies in this set because the norm is multiplicative and conjugation preserves the real part, which is zero for i. "
                    + "Conversely, let n be imaginary of norm one. If n is not -i, put q = 1 - n * i; a computation in components gives q * i * star q = |q|^2 n with |q|^2 = 2 (1 + n_i), where n_i is the i component of n, so this number is positive and the normalization q / |q| is a unit quaternion with Hopf image n. If n = -i, the unit quaternion j has Hopf image j * i * star j = -i. "
                    + "That the quadratic map of the three-sphere onto the two-sphere is surjective goes back to Hopf; the quaternion form of the map and the explicit preimages are derived here."),
            Node("homeomorph", "exists_homeomorph_quotient_phaseCircle", "The quotient by the phase circle is the two-sphere",
                StatementSource.FromAuthor(HomeomorphFormula()), AssessedProvenance.FromRepo(Hopf), DescribeRole.Theorem,
                "In the display, the quotient is the space of cosets x * phaseCircle with the quotient topology, mk(x) is the class of x, Homeomorph(A, B) is the type of homeomorphisms from A onto B, and the sphere on the right carries the subspace topology of the unit imaginary quaternions; the value e(mk(x)) is read as a quaternion. "
                    + "The statement is that some homeomorphism e from the quotient onto the unit imaginary sphere sends the class of every unit quaternion x to its Hopf image. "
                    + "Two unit quaternions have the same Hopf image exactly when they differ by a right factor in the phase circle: equal Hopf images give ray kernel one, by the expression of the ray kernel through the inner product of the Hopf images, and the ray kernel equals one exactly on the right phase cosets; conversely, a right phase factor gives ray kernel one, and two unit vectors with inner product one coincide. "
                    + "Hence the Hopf map descends to a continuous injection on the quotient, which is onto by the range theorem. The unit quaternions form the compact three-sphere and the target is Hausdorff, so this continuous bijection from a compact space is a homeomorphism. "
                    + "The fibres of the Hopf map are the great circles of Hopf's fibration; the description as right cosets of the phase circle and the homeomorphism statement are derived here."),
            Node("fibre-extremum", "rayKernel_isGreatest_and_integral", "Maximum and mean of the reading over a fibre",
                StatementSource.FromAuthor(ExtremumFormula()), AssessedProvenance.FromRepo(), DescribeRole.Theorem,
                "In the display, kappa and tri are the reading and the transfer of the quaternion comparison model, with kappa(x, y) = (1 + <x, y>) / 2 and tri(p, y, p) = p * y^-1 * p, IsGreatest(S, m) means that m belongs to S and bounds S from above, mk(a, b, c, d) is the quaternion a + b i + c j + d k, and the integration variable t runs over the interval from 0 to 2 pi. "
                    + "For all unit quaternions x and y the three conjuncts state: over the right phase circle of x, the round-trip reading kappa(y, (x c) y^-1 (x c)) has largest value rayKernel(x, y); the squared shifted reading (2 kappa(x c, y) - 1)^2 has the same largest value; and the integral over a full turn of the squared inner product of x (cos t + sin t i) with y equals pi times rayKernel(x, y). "
                    + "Put A = 2 kappa(x, y) - 1 and B = 2 kappa(x, y * i) - 1, so that rayKernel(x, y) = A^2 + B^2 by definition. For a phase c = a + b i one has 2 kappa(x c, y) - 1 = a A - b B, since right multiplication by a + b i mixes the inner products with y and with y * i. "
                    + "Over the circle a^2 + b^2 = 1 the square (a A - b B)^2 is at most A^2 + B^2 by the Cauchy-Schwarz inequality, with equality at a = A / r, b = -B / r for r the square root of A^2 + B^2, and at c = 1 when A = B = 0. "
                    + "For a unit quaternion p the round-trip identity kappa(y, p y^-1 p) = (2 kappa(p, y) - 1)^2 holds, because the real part of y^-1 p y^-1 p equals 2 <p, y>^2 - 1 for unit p and y; so the first set equals the second. "
                    + "Finally the squared inner product along the circle is A^2 cos^2 t + B^2 sin^2 t - 2 A B sin t cos t, whose integral over a full turn is pi (A^2 + B^2). "
                    + "Thus the ray kernel is both the fibre maximum of the round-trip reading and the mean of the squared inner product over the fibre, up to the factor pi; the module states no further property of the fibration."))));

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
    private static Formula HopfMap => Seq(Operatorname, Grp(F.Id("hopf")));
    private static Formula Model => Seq(Operatorname, Grp(F.Id("quaternionModel")));
    private static Formula Kappa(Formula x, Formula y) => Call("kappa", Model, x, y);
    private static Formula Tri(Formula p, Formula y, Formula q) => Call("tri", Model, p, y, q);
    private static Formula RayKernel(Formula x, Formula y) => Call("rayKernel", x, y);
    private static Formula Inner(Formula x, Formula y) =>
        new Formula.Subscript(Seq(Langle, Sp, x, Comma, Sp, y, Sp, Rangle), Reals);
    private static Formula UnitImaginary(string name)
    {
        Formula n = F.Id(name);
        return Seq(OpenBrace, n, Sp, InMacro, Sp, Quaternions, Sp, Mid, Sp,
            And(Equal(Call("re", n), D(0)), Equal(new Formula.Norm(n), D(1))), CloseBrace);
    }

    private static Formula PhaseCircleFormula()
    {
        Formula c = F.Id("c");
        return Disp(ForAll("c", Units, Logic(Rel(c, FormulaRelationOperator.MemberOf, PhaseCircle),
            FormulaLogicOperator.Iff, And(Equal(Call("imJ", c), D(0)), Equal(Call("imK", c), D(0))))));
    }

    private static Formula RangeFormula() => Disp(Equal(Call("range", HopfMap), UnitImaginary("n")));

    private static Formula HomeomorphFormula()
    {
        Formula e = F.Id("e"), x = F.Id("x");
        Formula quotient = Seq(Units, Sp, Slash, Sp, PhaseCircle);
        Formula homeomorphisms = Call("Homeomorph", quotient, UnitImaginary("n"));
        return Disp(Exists("e", homeomorphisms, ForAll("x", Units,
            Equal(new Formula.Apply(e, [Call("mk", x)]), Call("hopf", x)))));
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
