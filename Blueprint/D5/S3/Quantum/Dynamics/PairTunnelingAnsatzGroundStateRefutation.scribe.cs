using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class PairTunnelingAnsatzGroundStateRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Dynamics/PairTunnelingAnsatzGroundStateRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/volkoff2016pairtunnelling");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Volkoff's exact-ground-state conjecture for the two-mode pair-tunnelling ansatz fails in the eight-boson sector.",
        H("The pair-tunnelling ansatz fails at eight bosons"),
        Blocks(
            Node("factor", "Quadratic factors", FactorFormula(),
                "The variables X(0) and X(1) denote x and y in the complex polynomial ring on Fin 2; i is the complex imaginary unit. The Boolean s = false selects the +2icxy factor; s = true selects the -2icxy factor. Real parameters are embedded in the complex coefficients by ofReal. In each formula ite(s,a,b) selects a when s is true and b otherwise.",
                "ansatzFactor", DescribeRole.Definition),
            Node("polynomial", "The source polynomial", PolynomialFormula(),
                "Volkoff writes in Section V.A, pp. 6-7: \"Presently, we focus on the case of N even\" and defines Eq. (20): |ω_±(c)⟩ := 1/𝒩 [(a₀†² + 2ic a₀†a₁† − a₁†²)^M ± (a₀†² − 2ic a₀†a₁† − a₁†²)^M]|0,0⟩, where c ∈ ℝ, 𝒩 is a normalization factor, and M = N/2. Creation operators commute, so replacing them by x and y gives this polynomial. The displayed floor denotes natural-number division; only even N occurs in the conjecture. The Boolean s = false is the sum and s = true the difference.",
                "ansatzPolynomial", DescribeRole.Definition),
            Node("omega", "Fock amplitudes", OmegaFormula(),
                "The coefficient of x^(N-k)y^k is multiplied by √((N-k)!k!), because (a₀†)^(N-k)(a₁†)^k|0,0⟩ = √((N-k)!k!)|N-k,k⟩. The scalar normalization factor is omitted; nonzero scalar multiplication preserves membership of each eigenspace. Here coeff(m,P) is the coefficient of the exponent vector m in P, single(j,a) is the exponent vector supported at j with value a, and val(k) is the natural value of k : Fin(N+1). The operation tsub is truncated subtraction on natural numbers. Here ofNat denotes the natural-to-real embedding (Mathlib Nat.cast). All real square roots are embedded in ℂ by ofReal.",
                "omega", DescribeRole.Definition),
            Node("hamiltonian", "Pair tunnelling", HamiltonianFormula(),
                "The source studies \"the ground state of a₀†²a₁² + h.c.\" (Section V.A, p. 7). On |N-k,k⟩, a₁² contributes √(k(k-1)) and a₀†² contributes √((N-k+1)(N-k+2)); thus the transition to |N-k+2,k-2⟩ has their product. Replacing k by k+2 gives √((N-k-1)(N-k)(k+1)(k+2)). The adjoint supplies the reverse entry. Other entries vanish. The resulting matrix is real symmetric and hence Hermitian. The index arithmetic uses natural numbers and tsub denotes their truncated subtraction. Here ofNat denotes the natural-to-real embedding (Mathlib Nat.cast).",
                "pairTunnel", DescribeRole.Definition),
            Node("ground", "Exact ground state", GroundFormula(),
                "An exact ground state is a nonzero vector in an eigenspace with the least eigenvalue of the Hermitian Hamiltonian. This formula quantifies a real eigenvalue and compares it with every real eigenvalue having a nonzero eigenvector. Hermitian matrices have only real eigenvalues, so this is precisely the minimal-eigenvalue condition. The symbols mulVec and smul denote matrix action and complex scalar multiplication, respectively; Vector(N) abbreviates Fin(N+1) → ℂ only in these displays.",
                "IsGroundState", DescribeRole.Definition),
            Node("claim", "Volkoff's conjecture", ClaimFormula(),
                "Volkoff writes in Section V.A, p. 7: \"We conjecture that for each N ≥ 4 there exists a value c_N for which |ω_+(c_N)⟩ or |ω_−(c_N)⟩ is the exact ground state.\" The section fixes even N. The carrier is the full N-boson sector Fin(N+1) → ℂ; s = false/true encodes +/−, and the nonzero condition excludes the zero polynomial state.",
                "claim", DescribeRole.Definition),
            Node("result", "Refutation", Disp(new Formula.Not(F.Id("claim"))),
                "At N = 8, the positive factorial weights conjugate H to the coefficient action x²∂_y² + y²∂_x². For the sum state, its eigen-equations imply, with t = c², 10t² - 2t - 1 = 0 and 12t³ + 38t² - 12t - 3 = 0. Eliminating the cubic term forces 68t - 26 = 0, which contradicts the quadratic. For the difference state, c = 0 gives the zero vector; otherwise the eigen-equations force the eigenvalue -24t - 18 and 6t² + 4t - 3 = 0. Nonnegative t then satisfies t < 9/20, so the eigenvalue exceeds -144/5. The even and odd coefficient blocks satisfy the annihilating polynomials λ(λ² - 832)(λ² - 112) and λ⁴ - 904λ² + 63504, respectively. If λ < -8√13, then λ² > 832 and both polynomials are nonzero, forcing every eigenvector coordinate to vanish. Thus every real eigenvalue is at least -8√13. The coefficient vector (1,0,-4√13,0,30,0,-4√13,0,1), multiplied by the factorial weights, is a nonzero eigenvector at -8√13 < -144/5, so this is the exact ground energy. A ground-state ansatz would have to attain it. Both Boolean choices therefore fail.",
                "result", DescribeRole.Theorem, true,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("volkoff-2016-pair-tunneling-ansatz-ground-state-refutation"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, bool derived = false,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("volkoff-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula),
            derived ? AssessedProvenance.FromRepo(Source) : AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Num(int n) => new Formula.Number(n);
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Pow(Formula x, int n) => new Formula.Power(Parenthesized(x), Num(n));
    private static Formula Neg(Formula x) => Sub(Num(0), Parenthesized(x));
    private static Formula NeZero(Formula x) => new Formula.Not(Parenthesized(Eqn(x, Num(0))));
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complex() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Bool() => Named("Bool");
    private static Formula FinN(Formula n) => Call("Fin", Add(n, Num(1)));
    private static Formula Vector(Formula n) => new Formula.TypeArrow(FinN(n), Complex());
    private static Formula MatrixType(Formula n) => Call("Matrix", FinN(n), FinN(n), Complex());
    private static Formula Half(Formula n) => new Formula.Floor(new Formula.Fraction(n, Num(2)));
    private static Formula OfReal(Formula x) => Call("ofReal", x);
    private static Formula TSub(Formula a, Formula b) => Call("tsub", a, b);
    private static Formula Sqrt(Formula x) => Seq(F.Sqrt, Grp(x));
    private static Formula Factorial(Formula x) => Call("factorial", x);

    private static Formula FactorFormula()
    {
        Formula c = F.Id("c"), s = F.Id("s"), x = Call("X", Num(0)), y = Call("X", Num(1));
        Formula b = Mul(Mul(Num(2), F.Id("i")), OfReal(c));
        Formula factor = Sub(Add(Pow(x, 2), Mul(Mul(Call("C", Call("ite", s, Neg(b), b)), x), y)), Pow(y, 2));
        return Disp(All("c", Real(), All("s", Bool(), Eqn(Call("ansatzFactor", c, s), factor))));
    }

    private static Formula PolynomialFormula()
    {
        Formula n = F.Id("N"), s = F.Id("s"), c = F.Id("c");
        Formula a = new Formula.Power(Parenthesized(Call("ansatzFactor", c, F.Id("false"))), Half(n));
        Formula b = new Formula.Power(Parenthesized(Call("ansatzFactor", c, F.Id("true"))), Half(n));
        return Disp(All("N", Nat(), All("s", Bool(), All("c", Real(),
            Eqn(Call("ansatzPolynomial", n, s, c), Add(a, Call("ite", s, Neg(b), b)))))));
    }

    private static Formula OmegaFormula()
    {
        Formula n = F.Id("N"), s = F.Id("s"), c = F.Id("c"), k = F.Id("k"), v = Call("val", k);
        Formula weight = OfReal(Sqrt(Call("ofNat", Mul(Factorial(TSub(n, v)), Factorial(v)))));
        Formula exponent = Add(Call("single", Num(0), TSub(n, v)), Call("single", Num(1), v));
        return Disp(All("N", Nat(), All("s", Bool(), All("c", Real(), All("k", FinN(n),
            Eqn(Call("omega", n, s, c, k), Mul(weight, Call("coeff", exponent, Call("ansatzPolynomial", n, s, c)))))))));
    }

    private static Formula HamiltonianFormula()
    {
        Formula n = F.Id("N"), i = F.Id("j"), j = F.Id("k"), a = Call("val", i), b = Call("val", j);
        Formula Entry(Formula v) => OfReal(Sqrt(Call("ofNat", Mul(Mul(Mul(TSub(TSub(n, v), Num(1)), TSub(n, v)), Add(v, Num(1))), Add(v, Num(2))))));
        return Disp(All("N", Nat(), All("j", FinN(n), All("k", FinN(n),
            Eqn(Call("pairTunnel", n, i, j), Call("ite", Eqn(Add(a, Num(2)), b), Entry(a),
                Call("ite", Eqn(Add(b, Num(2)), a), Entry(b), Num(0))))))));
    }

    private static Formula GroundFormula()
    {
        Formula n = F.Id("N"), h = F.Id("H"), v = F.Id("v"), e = F.Id("eigen"), mu = F.Id("mu"), w = F.Id("w");
        Formula Eigen(Formula scalar, Formula state) => Eqn(Call("mulVec", h, state), Call("smul", OfReal(scalar), state));
        Formula body = And(NeZero(v), Ex("eigen", Real(), And(Eigen(e, v),
            All("mu", Real(), All("w", Vector(n), Implies(And(NeZero(w), Eigen(mu, w)), Le(e, mu)))))));
        return Disp(All("N", Nat(), All("H", MatrixType(n), All("v", Vector(n),
            Iff(Call("IsGroundState", h, v), body)))));
    }

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("N"), c = F.Id("c"), s = F.Id("s"), omega = Call("omega", n, s, c);
        Formula body = All("N", Nat(), Implies(Call("Even", n), Implies(Le(Num(4), n),
            Ex("c", Real(), Ex("s", Bool(), And(NeZero(omega), Call("IsGroundState", Call("pairTunnel", n), omega)))))));
        return Disp(Iff(F.Id("claim"), body));
    }
}
