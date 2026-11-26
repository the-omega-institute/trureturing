using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.AURICOmega;

internal sealed class QuaternionRayKernelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/AURICOmega/QuaternionRayKernel.";
    private static LibraryNoteRef Hopf => LibraryNoteRef.Create("D5/L/Topology/hopf1931abbildungen");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two-term squared reading of the quaternion comparison model depends only on the Hopf images, is blind to right phases in the span of 1 and i, and equals the trace pairing of two rank-one projections on complex two-space.",
        H("The phase-blind ray kernel on the unit quaternions"),
        Blocks(
            Node("hopf", "hopf", "The Hopf image of a unit quaternion",
                StatementSource.FromAuthor(HopfFormula()), AssessedProvenance.FromRepo(Hopf), DescribeRole.Definition,
                "For a unit quaternion x the Hopf image is the quaternion x * i * star x, where i is the unit quaternion unitI and star x = x^-1. "
                    + "It is the image of i under conjugation by x, so it is an imaginary quaternion of norm one. "
                    + "Writing x = a + b i + c j + d k, its i, j and k components are a^2 + b^2 - c^2 - d^2, 2 (a d + b c) and 2 (b d - a c); "
                    + "these are quadratic forms whose squares add up to (a^2 + b^2 + c^2 + d^2)^2, so x -> hopf x maps the unit three-sphere into the unit two-sphere of imaginary quaternions. As Hopf observed, the map is onto and its fibres are great circles."),
            Node("ray-kernel", "rayKernel", "The two-term squared reading",
                StatementSource.FromAuthor(RayKernelFormula()), AssessedProvenance.FromRepo(), DescribeRole.Definition,
                "The reading of the quaternion comparison model is kappa x y = (1 + <x, y>) / 2, so 2 * kappa x y - 1 is the real inner product <x, y>. "
                    + "The ray kernel adds its square to the square of the same expression after the second argument is multiplied on the right by i; "
                    + "thus rayKernel x y = <x, y>^2 + <x, y * i>^2."),
            Node("ray-kernel-eq-inner", "rayKernel_eq_inner", "The ray kernel through inner products",
                StatementSource.FromAuthor(RayKernelInnerFormula()), AssessedProvenance.FromRepo(), DescribeRole.Lemma,
                "Since kappa x y = (1 + <x, y>) / 2, the expression 2 * kappa x y - 1 equals <x, y>, and likewise 2 * kappa x (y * i) - 1 equals <x, y * i>, "
                    + "where the unit quaternion y * i, regarded as a quaternion, is the product of y and i. "
                    + "Substituting both into the definition gives the stated formula."),
            Node("ray-kernel-eq-hopf", "rayKernel_eq_hopf", "The ray kernel through the Hopf images",
                StatementSource.FromAuthor(RayKernelHopfFormula()), AssessedProvenance.FromRepo(), DescribeRole.Theorem,
                "For all quaternions p and q the polynomial identity <p, q>^2 + <p, q * i>^2 = (|p|^2 * |q|^2 + <p * i * star p, q * i * star q>) / 2 holds, as one checks by expanding both sides in the sixteen products of components. "
                    + "For unit quaternions |p| = |q| = 1, and the identity becomes the stated formula. "
                    + "In particular the ray kernel depends on x and y only through their Hopf images."),
            Node("phase-left", "rayKernel_mul_phase_left", "Blindness to a phase on the left argument",
                StatementSource.FromAuthor(PhaseLeftFormula()), AssessedProvenance.FromRepo(), DescribeRole.Theorem,
                "A quaternion c whose j and k components vanish lies in the real span of 1 and i and commutes with i. "
                    + "For a unit quaternion c of this kind, (x * c) * i * star (x * c) = x * (c * i * star c) * star x = x * i * star x, so right multiplication by c does not move the Hopf image. "
                    + "The formula through the Hopf images then gives the invariance."),
            Node("phase-right", "rayKernel_mul_phase_right", "Blindness to a phase on the right argument",
                StatementSource.FromAuthor(PhaseRightFormula()), AssessedProvenance.FromRepo(), DescribeRole.Theorem,
                "This is the same argument applied to the second argument: right multiplication of y by a unit quaternion c in the real span of 1 and i leaves the Hopf image of y unchanged."),
            Node("eq-one-iff", "rayKernel_eq_one_iff", "The ray kernel equals one exactly on the phase circles",
                StatementSource.FromAuthor(EqOneFormula()), AssessedProvenance.FromRepo(Hopf), DescribeRole.Theorem,
                "For all quaternions p and q the polynomial identity (star p * q)_j^2 + (star p * q)_k^2 = |p|^2 * |q|^2 - (<p, q>^2 + <p, q * i>^2) holds, where the subscripts denote the j and k components. "
                    + "If the ray kernel of the unit quaternions x and y equals one, the right side vanishes, so the j and k components of c = x^-1 * y = star x * y are both zero, as a sum of two squares that vanishes; and y = x * c. "
                    + "Conversely, if y = x * c with such a unit quaternion c, the phase invariance reduces the ray kernel to rayKernel x x = (1 + |hopf x|^2) / 2 = 1, since the Hopf image has norm one. "
                    + "It follows from this equivalence and the formula through the Hopf images, together with the equality case of the Cauchy-Schwarz inequality for the unit Hopf images, that two unit quaternions have the same Hopf image exactly when they differ by a right factor on the circle of unit quaternions in the span of 1 and i; this consequence is not among the formal statements of the module."),
            Node("spinor", "spinor", "Quaternions as complex two-vectors",
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), DescribeRole.Definition,
                "spinor is the real-linear isometric equivalence from the real quaternions to the Euclidean space of complex pairs indexed by Fin 2 that sends a + b i + c j + d k to the pair (a + b I, -c + d I), where I is the complex unit. "
                    + "Its inverse sends a pair (u, w) to the quaternion with components re u, im u, -re w and im w. "
                    + "It preserves norms because |a + b I|^2 + |-c + d I|^2 = a^2 + b^2 + c^2 + d^2."),
            Node("born-probability-spinor", "rayKernel_eq_bornProbability_spinor", "The ray kernel as a trace pairing of rank-one projections",
                StatementSource.FromAuthor(SpinorFormula()), AssessedProvenance.FromRepo(), DescribeRole.Theorem,
                "In the display ofLp is the coordinate vector of a point of the Euclidean space, vecMulVec v (star v) is the rank-one matrix with entries v a * conj (v b), dotProduct is the bilinear sum of products of coordinates, ofReal regards a real number as a complex number, and the Bloch vector of a complex two-by-two matrix M is (2 re M01, -2 im M01, re M00 - re M11). "
                    + "The four conjuncts hold for all unit quaternions x and y. "
                    + "First, multiplying q on the right by i multiplies the image pair by the complex unit, which is a direct computation in components. "
                    + "Second, the Bloch vector of the rank-one projection onto the image of x has coordinates the k, j and i components of the Hopf image of x, again by expanding both sides; "
                    + "since spinor x is a unit vector, this is the expression that the Bloch vector of a pure state takes, so together with the unit norm of Bloch vectors of pure states this identity implies that the coordinate vector of the Hopf image has norm one. "
                    + "Third, the complex transition amplitude star (spinor x) . spinor y has real part <x, y> and imaginary part -<x, y * i>, so its squared modulus is the ray kernel. "
                    + "Fourth, the trace of the product of the two rank-one projections onto spinor y and spinor x is the squared modulus of that amplitude, by the reduction of a rank-one branch weight on a rank-one pure state to a squared transition modulus."))));

    private static DocumentBlock Node(
        string id, string selector, string title, StatementSource statement,
        AssessedProvenance provenance, DescribeRole role, string prose) =>
        Describe.Lean(DescribeId.Create("quaternion-ray-kernel-" + id),
            DeclarationHandle.Create(Prefix + selector), H(title), statement, provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Rel(Formula x, FormulaRelationOperator op, Formula y) => new Formula.Relation(x, op, y);
    private static Formula Equal(Formula x, Formula y) => Rel(x, FormulaRelationOperator.Equal, y);
    private static Formula Logic(Formula x, FormulaLogicOperator op, Formula y) => new Formula.Logic(x, op, y);
    private static Formula And(Formula x, Formula y) => Logic(x, FormulaLogicOperator.And, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Square(Formula x) => new Formula.Power(x, D(2));
    private static Formula Half(Formula x) => new Formula.Fraction(x, D(2));
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
    private static Formula UnitI => Seq(Operatorname, Grp(F.Id("unitI")));
    private static Formula Model => Seq(Operatorname, Grp(F.Id("quaternionModel")));
    private static Formula Kappa(Formula x, Formula y) => Call("kappa", Model, x, y);
    private static Formula RayKernel(Formula x, Formula y) => Call("rayKernel", x, y);
    private static Formula HopfOf(Formula x) => Call("hopf", x);
    private static Formula Inner(Formula x, Formula y) =>
        new Formula.Subscript(Seq(Langle, Sp, x, Comma, Sp, y, Sp, Rangle), Reals);
    private static Formula Phase(Formula c) =>
        And(Equal(Call("imJ", c), D(0)), Equal(Call("imK", c), D(0)));
    private static Formula Vector(Formula x) => Call("ofLp", Call("spinor", x));
    private static Formula Projection(Formula x) => Call("vecMulVec", Vector(x), Call("star", Vector(x)));

    private static Formula HopfFormula()
    {
        Formula x = F.Id("x");
        return Disp(ForAll("x", Units, Equal(HopfOf(x), Mul(Mul(x, UnitI), Call("star", x)))));
    }

    private static Formula RayKernelFormula()
    {
        Formula x = F.Id("x"), y = F.Id("y");
        return Disp(ForAllMany(Units, Equal(RayKernel(x, y),
            Add(Square(Sub(Mul(D(2), Kappa(x, y)), D(1))),
                Square(Sub(Mul(D(2), Kappa(x, Mul(y, UnitI))), D(1))))), "x", "y"));
    }

    private static Formula RayKernelInnerFormula()
    {
        Formula x = F.Id("x"), y = F.Id("y");
        return Disp(ForAllMany(Units, Equal(RayKernel(x, y),
            Add(Square(Inner(x, y)), Square(Inner(x, Mul(y, UnitI))))), "x", "y"));
    }

    private static Formula RayKernelHopfFormula()
    {
        Formula x = F.Id("x"), y = F.Id("y");
        return Disp(ForAllMany(Units, Equal(RayKernel(x, y),
            Half(Add(D(1), Inner(HopfOf(x), HopfOf(y))))), "x", "y"));
    }

    private static Formula PhaseLeftFormula()
    {
        Formula x = F.Id("x"), y = F.Id("y"), c = F.Id("c");
        return Disp(ForAllMany(Units, Logic(Phase(c), FormulaLogicOperator.Implies,
            Equal(RayKernel(Mul(x, c), y), RayKernel(x, y))), "x", "y", "c"));
    }

    private static Formula PhaseRightFormula()
    {
        Formula x = F.Id("x"), y = F.Id("y"), c = F.Id("c");
        return Disp(ForAllMany(Units, Logic(Phase(c), FormulaLogicOperator.Implies,
            Equal(RayKernel(x, Mul(y, c)), RayKernel(x, y))), "x", "y", "c"));
    }

    private static Formula EqOneFormula()
    {
        Formula x = F.Id("x"), y = F.Id("y"), c = F.Id("c");
        return Disp(ForAllMany(Units, Logic(Equal(RayKernel(x, y), D(1)), FormulaLogicOperator.Iff,
            Exists("c", Units, And(Phase(c), Equal(y, Mul(x, c))))), "x", "y"));
    }

    private static Formula SpinorFormula()
    {
        Formula x = F.Id("x"), y = F.Id("y"), q = F.Id("q");
        Formula first = ForAll("q", Quaternions,
            Equal(Call("spinor", Mul(q, UnitI)), Mul(F.Id("I"), Call("spinor", q))));
        Formula h = HopfOf(x);
        Formula second = Equal(Call("bloch", Projection(x)),
            Call("toLp", D(2), Seq(Open, Call("imK", h), Comma, Sp, Call("imJ", h), Comma, Sp, Call("imI", h), Close)));
        Formula amplitude = Call("dotProduct", Call("star", Vector(x)), Vector(y));
        Formula third = Equal(RayKernel(x, y), Square(new Formula.Norm(amplitude)));
        Formula fourth = Equal(Call("ofReal", RayKernel(x, y)),
            Call("bornProbability", Projection(y), Projection(x)));
        return Disp(ForAllMany(Units, And(first, And(second, And(third, fourth))), "x", "y"));
    }
}
