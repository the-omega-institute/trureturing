using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class HiaiRuskaiRiemannianContractionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/QuantumChannels/HiaiRuskaiRiemannianContraction.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/hiairuskai2016contraction");
    private const string ConjectureQuote =
        "The arXiv v1 PDF, p. 19: \"Although the bounds in the above theorem are sufficient to disprove two conjectures as remarked below, we believe that they are optimal, i.e.,\" \"Conjecture 6.3. Equality holds in (45c) through (45e) above.\" The three equations below encode (45c), (45d), and (45e), respectively. Equation (45d) uses the geometric kernel fun x : ℝ => Real.rpow x (-1/2). Equation (45e) uses dslope Real.log 1, which equals Real.log x / (x - 1) away from x = 1 and has the continuous value 1 at x = 1. The carrier is Matrix (Fin 2) (Fin 2) C; the supremum ranges over every positive definite trace-one input and every nonzero traceless Hermitian tangent. Both signs of tau and alpha = 0 are included.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The dual WY, geometric and BKM Riemannian contraction coefficients of the non-unital qubit CQ channel equal the three bounds in Hiai and Ruskai's Conjecture 6.3. Each supremum is attained at the maximally mixed input and the Pauli X tangent.",
        H("Exact Riemannian contraction coefficients of a qubit CQ channel"),
        Blocks(
            Definition("omegaHermitian", "The operator in a Hermitian eigenbasis", OmegaHermitian(),
                "Section 2.4, p. 7: \"Given a function κ ∈ K we define, for any A ∈ P_d, a linear map Ω_A^κ : M_d → M_d by\" the displayed functional-calculus expression in the cited note. In the eigenbasis of rho, a matrix unit with indices i and j has eigenvalue k(lam i / lam j) / lam j. U is the unitary eigenvector matrix; lam is the eigenvalue function. The real coefficient is coerced to C before multiplication."),
            Definition("omega", "The spectral metric operator", Omega(),
                "The spectral definition agrees with the source's operator on positive definite matrices. Its value at a non-Hermitian foot point is zero; only positive definite foot points occur in the contraction coefficient."),
            Definition("phi", "The qubit CQ channel", PhiFormula(),
                "Section 6, p. 19: \"The next theorem treats a family of trace-preserving maps Φ_{α,τ} : M_2 → M_2 with two real parameters α,τ determined by t = (0,0,τ)^t and T = diag(α,0,0); more explicitly,\" followed by the channel equation quoted in the cited note. The coefficients w0 = trace X / 2 and w1 = trace (qubitX * X) / 2 give the complex linear extension to all matrices. qubitX and qubitZ are the Pauli matrices from FiniteDimensional."),
            Definition("metric", "The real metric quadratic form", Metric(),
                "Section 2.4, p. 8: \"Associated with κ ∈ K a Riemannian metric M^κ on the Riemannian manifold D_d is defined by\" equation (17), quoted in the cited note. The diagonal quadratic form is the Hilbert-Schmidt pairing of A with Omega(A). The displayed trace has zero imaginary part, so its real part is the source's quadratic form."),
            Definition("ratio", "An input's contraction ratio", Ratio(),
                "The numerator evaluates the same kernel at the channel image of the state and tangent. The denominator is strictly positive for each of the three kernels, every positive definite input and every nonzero tangent."),
            Definition("eta", "The Riemannian contraction coefficient", Eta(),
                "Section 2.4, p. 8: \"For each κ ∈ K the contraction coefficient of a CPT map Φ with respect to the monotone metric M^κ induced by κ is defined by\" equation (19), quoted in the cited note. The supremum runs over rho in the strict density domain and A in the traceless Hermitian space with A nonzero. The subtype value operation exposes the underlying matrix; no input or tangent is restricted to a chosen Pauli direction."),
            Definition("kDualWY", "The dual Wigner-Yanase kernel", Kernel("kDualWY",
                Frac(Square(Add(D(1), Call("Real.sqrt", Id("x")))), Mul(D(4), Id("x")))),
                "Theorem 6.2, equation (45c): the dual WY kernel is (1 + sqrt x)^2 / (4 x)."),
            Definition("admissible", "The non-unital channel parameters", AdmissibleDefinition(),
                "Section 6, p. 19: \"Below we assume that α ≥ 0 and α² + τ² ≤ 1.\" The nonsingular non-unital range is 0 < |tau| < 1. There is no strict positivity condition on alpha."),
            Definition("claim", "Hiai-Ruskai Conjecture 6.3", Disp(Iff(Id("claim"), ClaimBody())), ConjectureQuote),
            Describe.Lean(DescribeId.Create("hiai-ruskai-result"), DeclarationHandle.Create(Prefix + "result"),
                H("All three bounds are exact"), StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every extreme kernel, a scalar pinching identity bounds the input metric below by 4 y1^2 / (1 - w1^2), and the exact output formula bounds the numerator by the extreme coefficient times that same quantity. Integrating both inequalities with the positive geometric and BKM weights preserves their common denominator. The BKM kernel is dslope Real.log 1. The dual WY kernel is the half mixture of the zero extreme kernel and fun x : ℝ => Real.rpow x (-1/2). The common pair rho = I/2 and A = qubitX attains every upper bound. The argument treats alpha = 0 and both signs of tau."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("hiai-ruskai-2015-cq-contraction-coefficients"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Definition(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("hiai-ruskai-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula Id(string name) => F.Id(name);
    private static Formula Named(string name)
    {
        var items = new List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Apply(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula formula) => Seq(Open, formula, Close);
    private static Formula Reals() => Seq(Mathbb, Grp(Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(Id("C")));
    private static Formula QubitMatrix() => Call("Matrix", Call("Fin", D(2)), Call("Fin", D(2)), Complexes());
    private static Formula Kernels() => new Formula.TypeArrow(Reals(), Reals());
    private static Formula All(string variable, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), type, body);
    private static Formula Some(string variable, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(variable), type, body);
    private static Formula Eq(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Ne(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Lt(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Le(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Frac(Formula left, Formula right) => new Formula.Fraction(left, right);
    private static Formula Square(Formula x) => new Formula.Power(Parenthesized(x), D(2));
    private static Formula ToComplex(Formula x) => Parenthesized(Seq(x, Sp, Colon, Sp, Complexes()));
    private static Formula Hermitian(Formula x) => Call("Matrix.IsHermitian", x);
    private static Formula StarMatrix(Formula x) => Call("Matrix.conjTranspose", x);
    private static Formula Smul(Formula scalar, Formula matrix) => Call("SMul.smul", scalar, matrix);
    private static Formula Lambda(string name, Formula type, Formula body) =>
        Seq(Id("fun"), Sp, Parenthesized(Seq(Id(name), Sp, Colon, Sp, type)), Sp, Mapsto, Sp, body);
    private static Formula Let(string name, Formula value, Formula body) =>
        Seq(Id("let"), Sp, Id(name), Sp, Colon, F.Eq, Sp, value, Semi, Sp, body);
    private static Formula KMatrixDefinition(string name, Formula body) =>
        Disp(All("k", Kernels(), All("rho", QubitMatrix(), All("A", QubitMatrix(),
            Eq(Call(name, Id("k"), Id("rho"), Id("A")), body)))));

    private static Formula OmegaHermitian()
    {
        var k = Id("k"); var rho = Id("rho"); var h = Id("h"); var x = Id("X");
        var u = Id("U"); var lam = Id("lam"); var y = Id("Y"); var z = Id("Z");
        var i = Id("i"); var j = Id("j");
        var coefficient = ToComplex(Frac(Apply(k, Frac(Apply(lam, i), Apply(lam, j))), Apply(lam, j)));
        var entry = Mul(coefficient, Apply(y, i, j));
        var body = Let("U", Parenthesized(Seq(Call("Matrix.IsHermitian.eigenvectorUnitary", h), Sp, Colon, Sp, QubitMatrix())),
            Let("lam", Call("Matrix.IsHermitian.eigenvalues", h),
            Let("Y", Mul(Mul(StarMatrix(u), x), u),
            Let("Z", Lambda("i", Call("Fin", D(2)), Lambda("j", Call("Fin", D(2)), entry)),
                Mul(Mul(u, z), StarMatrix(u))))));
        return Disp(All("k", Kernels(), All("rho", QubitMatrix(), All("h", Hermitian(rho),
            All("X", QubitMatrix(), Eq(Call("omegaHermitian", k, rho, h, x), body))))));
    }
    private static Formula Omega()
    {
        var k = Id("k"); var rho = Id("rho"); var x = Id("X"); var h = Id("h");
        var body = Seq(Id("if"), Sp, h, Sp, Colon, Sp, Hermitian(rho), Sp, Id("then"), Sp,
            Call("omegaHermitian", k, rho, h, x), Sp, Id("else"), Sp, D(0));
        return Disp(All("k", Kernels(), All("rho", QubitMatrix(), All("X", QubitMatrix(),
            Eq(Call("omega", k, rho, x), body)))));
    }
    private static Formula PhiFormula()
    {
        var alpha = Id("alpha"); var tau = Id("tau"); var x = Id("X"); var wzero = Id("wzero"); var wone = Id("wone");
        var sx = Named("D5.S3.Quantum.FiniteDimensional.qubitX");
        var sz = Named("D5.S3.Quantum.FiniteDimensional.qubitZ");
        var identity = Parenthesized(Seq(D(1), Sp, Colon, Sp, QubitMatrix()));
        var body = Let("wzero", Frac(Call("Matrix.trace", x), D(2)),
            Let("wone", Frac(Call("Matrix.trace", Mul(sx, x)), D(2)),
                Add(Add(Smul(wzero, identity), Smul(Mul(ToComplex(alpha), wone), sx)), Smul(Mul(ToComplex(tau), wzero), sz))));
        return Disp(All("alpha", Reals(), All("tau", Reals(), All("X", QubitMatrix(), Eq(Call("phi", alpha, tau, x), body)))));
    }
    private static Formula Metric() => KMatrixDefinition("metric",
        Call("Complex.re", Call("Matrix.trace", Mul(StarMatrix(Id("A")), Call("omega", Id("k"), Id("rho"), Id("A"))))));
    private static Formula Ratio()
    {
        var k = Id("k"); var alpha = Id("alpha"); var tau = Id("tau"); var rho = Id("rho"); var a = Id("A");
        var body = Frac(Call("metric", k, Call("phi", alpha, tau, rho), Call("phi", alpha, tau, a)), Call("metric", k, rho, a));
        return Disp(All("k", Kernels(), All("alpha", Reals(), All("tau", Reals(), All("rho", QubitMatrix(),
            All("A", QubitMatrix(), Eq(Call("ratio", k, alpha, tau, rho, a), body)))))));
    }
    private static Formula StrictDensities()
    {
        var rho = Id("rho");
        return Seq(OpenBrace, rho, Sp, Colon, Sp, QubitMatrix(), Sp, Slash, Slash, Sp,
            And(Call("Matrix.PosDef", rho), Eq(Call("Matrix.trace", rho), D(1))), CloseBrace);
    }
    private static Formula Eta()
    {
        var k = Id("k"); var alpha = Id("alpha"); var tau = Id("tau"); var z = Id("z"); var rho = Id("rho"); var a = Id("A");
        var predicate = And(And(Hermitian(a), Eq(Call("Matrix.trace", a), D(0))),
            And(Ne(a, D(0)), Eq(z, Call("ratio", k, alpha, tau, Call("Subtype.val", rho), a))));
        var values = Seq(OpenBrace, z, Sp, Colon, Sp, Reals(), Sp, Mid, Sp,
            Some("rho", StrictDensities(), Some("A", QubitMatrix(), predicate)), CloseBrace);
        return Disp(All("k", Kernels(), All("alpha", Reals(), All("tau", Reals(),
            Eq(Call("eta", k, alpha, tau), Call("sSup", values))))));
    }
    private static Formula Kernel(string name, Formula body) => Disp(All("x", Reals(), Eq(Call(name, Id("x")), body)));
    private static Formula AdmissibleBody()
    {
        var alpha = Id("alpha"); var tau = Id("tau"); var absolute = new Formula.Absolute(tau);
        return And(Le(D(0), alpha), And(Lt(D(0), absolute), And(Lt(absolute, D(1)), Le(Add(Square(alpha), Square(tau)), D(1)))));
    }
    private static Formula AdmissibleDefinition() => Disp(All("alpha", Reals(), All("tau", Reals(),
        Iff(Call("admissible", Id("alpha"), Id("tau")), AdmissibleBody()))));
    private static Formula ClaimBody()
    {
        var alpha = Id("alpha"); var tau = Id("tau"); var gap = Sub(D(1), Square(tau)); var root = Call("Real.sqrt", gap);
        var dual = Eq(Call("eta", Named("kDualWY"), alpha, tau), Frac(Mul(Square(alpha), Add(D(1), root)), Mul(D(2), gap)));
        var geometric = Eq(Call("eta", Lambda("x", Reals(), Call("Real.rpow", Id("x"), Sub(D(0), Frac(D(1), D(2))))), alpha, tau), Frac(Square(alpha), root));
        var bkm = Eq(Call("eta", Call("dslope", Named("Real.log"), D(1)), alpha, tau),
            Frac(Mul(Square(alpha), Call("Real.log", Frac(Add(D(1), tau), Sub(D(1), tau)))), Mul(D(2), tau)));
        return All("alpha", Reals(), All("tau", Reals(), Implies(Call("admissible", alpha, tau), And(dual, And(geometric, bkm)))));
    }
}
