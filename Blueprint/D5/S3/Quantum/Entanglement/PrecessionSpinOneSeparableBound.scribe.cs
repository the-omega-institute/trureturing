using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class PrecessionSpinOneSeparableBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/PrecessionSpinOneSeparableBound.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/huynhvu2024precession");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The spin-1 tensor spin-K/2 precession protocol has separable bound ½ [1 + 2^{−(K−1)} binom(K−1, (K−1)/2) (K−1)/(K+1)] for every odd K ≥ 7. This is Conjecture 2, Eq. (32), of Huynh-Vu, Zaw and Scarani (arXiv:2311.00806v2).",
        H("Spin-1 tensor spin-K/2 precession separable bound"),
        Blocks(
            Node("Jplus", "Spin raising matrix", JplusFormula(),
                "In the standard descending |j,m⟩ basis the raising matrix has entry √(j(j+1)−m(m+1)) on the one-step superdiagonal, with j = n/2, m = j−r and ℏ = 1.", DescribeRole.Definition),
            Node("Jx", "Spin x matrix", JxFormula(),
                "Jx is the Hermitian half-sum of the raising matrix and its conjugate transpose.", DescribeRole.Definition),
            Node("Jy", "Spin y matrix", JyFormula(),
                "Jy is the Hermitian y component obtained from the raising matrix and its conjugate transpose.", DescribeRole.Definition),
            Node("Jz", "Spin z matrix", JzFormula(),
                "Jz is diagonal in the standard basis with entries n/2 minus the descending index.", DescribeRole.Definition),
            Node("rotation", "Spin z rotation", RotationFormula(),
                "The diagonal spin rotation has phase exp(-I angle (n/2-i.val)) in the descending spin basis.", DescribeRole.Definition),
            Node("total", "Total angular momentum", TotalFormula(),
                "The total operator is J on the tensor product, J^(1) ⊗ I + I ⊗ J^(K/2), represented by the Kronecker sum.", DescribeRole.Definition),
            Node("theta", "Precession angle", ThetaFormula(),
                "The k-th protocol angle is 2πk/K for k in Fin K. NatCast is the natural-to-real cast; ofReal is the real-to-complex cast. val is the underlying natural index, and n is twice the spin.", DescribeRole.Definition),
            Node("Jk", "Precessed observable", JkFormula(),
                "The protocol uses J_k = cos(2πk/K)J_x + sin(2πk/K)J_y.", DescribeRole.Definition),
            Node("positiveWeight", "Positive spectral weight", PositiveWeightFormula(),
                "The positive projector weights positive eigenvalues by one, zero by one half, and negative eigenvalues by zero.", DescribeRole.Definition),
            Node("pos", "Positive spectral projector", PosFormula(),
                "For a Hermitian J, pos(J) = Σ_{λ>0} P_λ(J) + ½ P_0(J), with the source’s half weight at zero. The definition requires a proof h of Hermiticity and is exactly h.cfc positiveWeight. The finite spectrum requires no continuity hypothesis; its spectral expression is U diag(positiveWeight(eigenvalues)) Uᴴ. All protocol observables are Hermitian.", DescribeRole.Definition),
            Node("Q", "Protocol average", QFormula(),
                "Q_K is the average of the positive spectral projectors over k in Fin K.", DescribeRole.Definition),
            Node("productVector", "Product vector", ProductVectorFormula(),
                "The tensor product of a spin-1 vector and a spin-K/2 vector is represented in the product basis by pointwise multiplication of the two coordinates.", DescribeRole.Definition),
            Node("scores", "Separable score set", ScoresFormula(),
                "The score set consists of real quadratic expectations on unit product vectors in ℂ³ ⊗ ℂ^(K+1).", DescribeRole.Definition),
            Node("c", "Central binomial coefficient", CFormula(),
                "c K is 2^{−(K−1)} times the central binomial coefficient. Both K−1 and Nat.div use natural arithmetic (Nat.div is floor division); NatCast casts the binomial coefficient into ℝ.", DescribeRole.Definition),
            Node("claim", "Huynh-Vu–Zaw–Scarani Conjecture 2",
                ClaimFormula(),
                "The source states: \"The separable bound for {ȷ̃, ȷ̃′} = {1, K/2} with K ≥ 7 is Psep_K({1, K/2}) = ½ [1 + 2^{−(K−1)} binom(K−1, (K−1)/2) (K−1)/(K+1)].\" The source defines the precession protocol by \"Jk := e^{−i(2πk/K)Jz/ℏ} Jx e^{i(2πk/K)Jz/ℏ} = cos(2πk/K)Jx + sin(2πk/K)Jy, where k ∈ {0, 1, . . . , K − 1}.\" Equations (2)–(3) state \"PK := (1/K) Σ_{k=0}^{K−1} [Pr(Jk > 0) + ½ Pr(Jk = 0)], QK := (1/K) Σ_k pos(Jk),\" and \"Here, pos(Jk) is defined on the eigenstates |j, m⟩k of Jk, such that Jk|j, m⟩k = ℏm|j, m⟩k and 2 pos(Jk)|j, m⟩k = [1+sgn(m)]|j, m⟩k, with the usual convention sgn(0) = 0.\" Conjecture 2 and Eq. (32) are in arXiv v2, §III, PDF p. 8; Eqs. (1)–(3) are on PDF p. 2. The Lean statement binds the natural indices, casts them into ℝ for the final expression, and uses natural-number division in c.",
                DescribeRole.Definition),
            Node("result", "Proof of the separable bound", Disp(F.Id("claim")),
                "The proof diagonalizes the spin-K/2 Jx operator with the binomial eigenbasis, evaluates the rotation average by the K-th root-of-unity filter, decomposes the half-integer sign spectrum, and compresses the product quadratic form to a six-index off-diagonal block. The squared Frobenius estimate is convex in |a₁|² for K ≥ 7 and is attained by the spin-1 middle state and an endpoint singular vector.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("huynh-vu-zaw-scarani-2023-precession-separable-bound"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("precession-" + id.ToLowerInvariant()), DeclarationHandle.Create(Prefix + id),
            H(title), StatementSource.FromAuthor(formula), provenance ?? AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(Formula name) => Seq(Operatorname, Grp(name));
    private static Formula Call(Formula name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Call(string name, params Formula[] args) => Call(F.Id(name), args);
    private static Formula Qualified(string scope, string name) => Seq(F.Id(scope), Dot, F.Id(name));
    private static Formula QualifiedCall(string scope, string name, params Formula[] args) =>
        new Formula.Apply(Named(Qualified(scope, name)), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Bound(Formula name, Formula type) => Seq(name, Colon, Sp, type);
    private static Formula Eq(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Lt(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Ge(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.GreaterThanOrEqual, right);
    private static Formula And(params Formula[] terms) => terms.Reverse().Aggregate((right, left) => new Formula.Logic(left, FormulaLogicOperator.And, right));
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Exists(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Lambda(string name, Formula type, Formula body) =>
        Seq(Parenthesized(Bound(F.Id(name), type)), Sp, Mapsto, Sp, body);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complex() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Type() => F.Id("Type");
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula SpinIndex(Formula n) => Fin(Parenthesized(Seq(n, Sp, Plus, Sp, D(1))));
    private static Formula SpinMatrix(Formula n) => Call("Matrix", SpinIndex(n), SpinIndex(n), Complex());
    private static Formula Euclidean(Formula n) => Call("EuclideanSpace", Complex(), SpinIndex(n));
    private static Formula OfReal(Formula x) => Call("ofReal", x);
    private static Formula NatCast(Formula x) => Call("NatCast", x);
    private static Formula Val(Formula x) => Call("val", x);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Div(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula Smul(Formula x, Formula y) => Call("smul", x, y);
    private static Formula ComplexScalar(Formula value) => Parenthesized(Seq(value, Colon, Sp, Complex()));
    private static Formula MatrixScalar(Formula value, Formula n) => Parenthesized(Seq(value, Colon, Sp, SpinMatrix(n)));
    private static Formula ConjTranspose(Formula x) => Call("conjTranspose", x);
    private static Formula If(Formula condition, Formula yes, Formula no) => Call("if", condition, yes, no);
    private static Formula Instances(Formula type) => Seq(OpenBracket, Call("Fintype", type), CloseBracket, Sp,
        OpenBracket, Call("DecidableEq", type), CloseBracket, Sp);

    private static Formula JplusFormula()
    {
        var n = F.Id("n"); var i = F.Id("i"); var r = F.Id("r");
        var j = Div(NatCast(n), D(2));
        var m = Sub(j, NatCast(Val(r)));
        var radicand = Sub(Mul(j, Parenthesized(Add(j, D(1)))),
            Mul(Parenthesized(m), Parenthesized(Add(m, D(1)))));
        var entry = If(
            Eq(Add(Val(i), D(1)), Val(r)),
            OfReal(QualifiedCall("Real", "sqrt", radicand)),
            D(0));
        var matrix = Lambda("i", Fin(Parenthesized(Add(n, D(1)))), Lambda("r", Fin(Parenthesized(Add(n, D(1)))), entry));
        return Disp(All("n", Nat(), Eq(Call("Jplus", n), matrix)));
    }

    private static Formula JxFormula()
    {
        var n = F.Id("n"); var j = Call("Jplus", n);
        return Disp(All("n", Nat(), Eq(Call("Jx", n), Smul(ComplexScalar(Div(D(1), D(2))), Parenthesized(Add(j, ConjTranspose(j)))))));
    }

    private static Formula JyFormula()
    {
        var n = F.Id("n"); var j = Call("Jplus", n);
        return Disp(All("n", Nat(), Eq(Call("Jy", n), Smul(ComplexScalar(Div(D(1), Mul(D(2), F.Id("I")))), Parenthesized(Sub(j, ConjTranspose(j)))))));
    }

    private static Formula JzFormula()
    {
        var n = F.Id("n"); var i = F.Id("i");
        var value = OfReal(Sub(Div(NatCast(n), D(2)), NatCast(Val(i))));
        return Disp(All("n", Nat(), Eq(Call("Jz", n), Call("diagonal", Lambda("i", SpinIndex(n), value)))));
    }

    private static Formula RotationFormula()
    {
        var n = F.Id("n"); var angle = F.Id("angle"); var i = F.Id("i");
        var spin = ComplexScalar(Parenthesized(Seq(Sub(Div(Parenthesized(Seq(n, Colon, Sp, Real())), D(2)), Parenthesized(Seq(Val(i), Colon, Sp, Real()))), Colon, Sp, Real())));
        var exponent = Mul(Mul(Seq(Minus, Qualified("Complex", "I")), ComplexScalar(angle)), spin);
        return Disp(All("n", Nat(), All("angle", Real(), Eq(Call("rotation", n, angle),
            QualifiedCall("Matrix", "diagonal", Lambda("i", SpinIndex(n), QualifiedCall("Complex", "exp", exponent)))))));
    }

    private static Formula TotalFormula()
    {
        var k = F.Id("K"); var a = F.Id("A"); var b = F.Id("B");
        var body = Add(Call("kronecker", a, MatrixScalar(D(1), k)), Call("kronecker", MatrixScalar(D(1), D(2)), b));
        return Disp(All("K", Nat(), All("A", SpinMatrix(D(2)), All("B", SpinMatrix(k), Eq(Call("total", k, a, b), body)))));
    }

    private static Formula ThetaFormula()
    {
        var k = F.Id("K"); var i = F.Id("k");
        return Disp(All("K", Nat(), All("k", Fin(k), Eq(Call("theta", k, i), Div(Mul(Mul(D(2), Qualified("Real", "pi")), NatCast(Val(i))), NatCast(k))))));
    }

    private static Formula JkFormula()
    {
        var k = F.Id("K"); var i = F.Id("k");
        var body = Add(Smul(OfReal(QualifiedCall("Real", "cos", Call("theta", k, i))), Call("total", k, Call("Jx", D(2)), Call("Jx", k))),
            Smul(OfReal(QualifiedCall("Real", "sin", Call("theta", k, i))), Call("total", k, Call("Jy", D(2)), Call("Jy", k))));
        return Disp(All("K", Nat(), All("k", Fin(k), Eq(Call("Jk", k, i), body))));
    }

    private static Formula PositiveWeightFormula()
    {
        var x = F.Id("x");
        return Disp(All("x", Real(), Eq(Call("positiveWeight", x), If(Lt(D(0), x), D(1), If(Eq(x, D(0)), Div(D(1), D(2)), D(0))))));
    }

    private static Formula PosFormula()
    {
        var ι = F.Id("T"); var h = F.Id("H");
        var matrix = Call("Matrix", ι, ι, Complex());
        var value = Call(Seq(F.Id("h"), Dot, F.Id("cfc")), F.Id("positiveWeight"));
        return Disp(All("T", Type(), Seq(Instances(ι), All("H", matrix,
            All("h", Call("IsHermitian", h), Eq(Call("pos", F.Id("h")), value))))));
    }

    private static Formula QFormula()
    {
        var k = F.Id("K"); var i = F.Id("k");
        var sum = Seq(new Formula.Subscript(Sum, Seq(i, Colon, Sp, Fin(k))), Sp, Call("pos", Call("Jk", k, i)));
        return Disp(All("K", Nat(), Eq(Call("Q", k), Smul(ComplexScalar(Div(D(1), ComplexScalar(k))), sum))));
    }

    private static Formula ProductVectorFormula()
    {
        var k = F.Id("K"); var a = F.Id("a"); var b = F.Id("b"); var i = F.Id("i");
        var index = Call("Prod", SpinIndex(D(2)), SpinIndex(k));
        var body = QualifiedCall("WithLp", "toLp", D(2), Lambda("i", index,
            Mul(Call("a", Call("fst", i)), Call("b", Call("snd", i)))));
        return Disp(All("K", Nat(), All("a", Euclidean(D(2)), All("b", Euclidean(k), Eq(Call("productVector", k, a, b), body)))));
    }

    private static Formula ScoresFormula()
    {
        var k = F.Id("K"); var t = F.Id("t"); var a = F.Id("a"); var b = F.Id("b");
        var pv = Call("productVector", k, a, b);
        var pvOfLp = Seq(Parenthesized(pv), Dot, F.Id("ofLp"));
        var score = Eq(t, Call("re", Parenthesized(Call("dotProduct",
            Call("star", pvOfLp), Call("mulVec", Call("Q", k), pvOfLp)))));
        var body = Seq(OpenBrace, Bound(t, Real()), Sp, Mid, Sp,
            Exists("a", Euclidean(D(2)), Exists("b", Euclidean(k),
                And(Parenthesized(Eq(new Formula.Norm(a), D(1))),
                    Parenthesized(Eq(new Formula.Norm(b), D(1))), Parenthesized(score)))), CloseBrace);
        return Disp(All("K", Nat(), Eq(Call("scores", k), body)));
    }

    private static Formula CFormula()
    {
        var k = F.Id("K");
        var km1 = Parenthesized(Sub(k, D(1)));
        var central = Seq(new Formula.Fraction(D(1), new Formula.Power(D(2), km1)), Sp,
            Call("NatCast", QualifiedCall("Nat", "choose", km1, QualifiedCall("Nat", "div", km1, D(2)))));
        return Disp(All("K", Nat(), Eq(Call("c", k), central)));
    }

    private static Formula ClaimFormula()
    {
        var k = F.Id("K");
        var km1 = Parenthesized(Sub(k, D(1)));
        var kp1 = Parenthesized(Add(k, D(1)));
        var central = Call(F.Id("c"), k);
        var ratio = Div(NatCast(km1), NatCast(kp1));
        var bound = Seq(Frac, Grp(D(1)), Grp(D(2)), Sp,
            Parenthesized(Seq(D(1), Sp, Plus, Sp, central, Sp, ratio)));
        var body = All("K", Nat(), new Formula.Logic(Call(F.Id("Odd"), k), FormulaLogicOperator.Implies,
            new Formula.Logic(Ge(k, D(7)), FormulaLogicOperator.Implies, Call(F.Id("IsGreatest"), Call(F.Id("scores"), k), bound))));
        return Disp(new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff, Parenthesized(body)));
    }

}
