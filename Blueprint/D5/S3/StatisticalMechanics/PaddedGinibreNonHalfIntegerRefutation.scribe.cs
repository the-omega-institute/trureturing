using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics;

internal sealed class PaddedGinibreNonHalfIntegerRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/PaddedGinibreNonHalfIntegerRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/abdesselam2022nonabelian");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The padded general Ginibre inequalities for stable determinantal polynomials fail at exponent 1/4. Three positive semidefinite real matrices of size two, a positive definite sum, trivial parity and four rows give a strictly negative PGG sum.",
        H("A non-half-integer exponent violates the PGG inequalities"),
        Blocks(
            Node("polynomial", "Determinantal polynomial", PolynomialFormula(),
                """Page 9: "Let q ∈ ℕ_{>0}, and let A₁, …, Aₙ be n real symmetric positive semidefinite matrices of q × q format. Suppose that A₁ + ⋯ + Aₙ is positive definite and define the polynomial P(x) = det(x₁A₁ + ⋯ xₙAₙ) which is then strictly positive for x ∈ (0, ∞)ⁿ." Here A is an explicit argument, its indices run over Fin(n), x has real coordinates, and each A_j is a Matrix(Fin(q), Fin(q), R).""",
                "P", AssessedProvenance.FromLiterature(Source)),
            Node("parity", "Even multi-indices", ParityFormula(),
                """Page 5: "Suppose we are given a group homomorphism ρ : ℤⁿ → (ℤ/2ℤ)ᴸ, for some integer L ≥ 0." "We will say that a is even iff ρ(a) = 0." The carrier is the additive homomorphism (Fin(n) -> Z) ->+ (Fin(L) -> ZMod(2)); castInt casts each natural coordinate of a to an integer. L = 0 is allowed.""",
                "evenIndex", AssessedProvenance.FromLiterature(Source)),
            Node("sum", "The padded general Ginibre sum", SumFormula(),
                "The sum in Theorem 2.3 (p. 10) uses pairs of natural vectors alpha + beta = 1_m and the sign epsilon^beta = product_i epsilon_i^{beta_i} (p. 6). Here alpha : Fin(m) -> Fin(2) indexes each pair once, val(alpha_i) is its natural value, and beta_i = 1 - val(alpha_i); this subtraction is in N and has no truncation because val(alpha_i) is 0 or 1. Vector-matrix multiplication vecMul(a,V) is Mathlib Matrix.vecMul: its j-th coordinate is the sum of a_i V_ij. The indicator is 1 for an even alpha V and 0 otherwise. castReal casts the natural padded coordinates and integer signs to R, and all powers with exponent -eta are Real.rpow.",
                "pggSum", AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Problem 3: arbitrary positive real exponents", ClaimFormula(),
                """Page 14: "Problem 3: In the light of investigations of spin models with non-integer number of components N, as in [8], it would be interesting to see if Thm. 2.3 still holds for P^{−η} where η is any positive real number instead of being restricted to half integers." The displayed claim keeps every quantifier and hypothesis of Theorem 2.3 (p. 10): eta > 0, n, q and L in N, q > 0, every A_j positive semidefinite, their sum positive definite, every m, natural V, integer signs in {-1,1}, positive natural u, and even 1_m V and u. Here const(Fin(m),1) denotes Mathlib Function.const (Fin m) (1 : ℕ). For real matrices PosSemidef includes symmetry, and PosDef includes strict positivity on every nonzero vector. Fin indices are zero-based; no condition n > 0 or m > 0 is added. The binary convention for the sum is stated above.""",
                "claim", AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("pgg-result"), DeclarationHandle.Create(Prefix + "result"),
                H("The extension to every positive exponent is false"),
                StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Take eta = 1/4, n = 3, q = 2, L = 0, m = 4, the zero parity map, u = (1,1,1), every epsilon_i = -1, and rows V = (1,0,0), (1,0,0), (0,1,0), (0,0,1). The matrices are [[1,0],[0,0]], [[0,0],[0,1]], [[1,1],[1,1]]. Their quadratic forms are v_0^2, v_1^2, (v_0+v_1)^2; the sum has form v_0^2 + v_1^2 + (v_0+v_1)^2 and is positive definite. The determinant is x_0 x_1 + x_0 x_2 + x_1 x_2. The sixteen terms combine into Theta = 2*48^(-1/4) - 4*55^(-1/4) + 2*56^(-1/4) - 4*60^(-1/4) + 4*64^(-1/4). Integer fourth-power comparisons give 48*3800^4, 56*3656^4, 64*3536^4 > 10^16 and 55*3672^4, 60*3593^4 < 10^16. Monotonicity of the fourth power gives upper bounds for the three powers with positive coefficients and lower bounds for the two powers with negative coefficients, so Theta < (2*3800 - 4*3672 + 2*3656 - 4*3593 + 4*3536)/10000 = -1/2500 < 0."))),
                DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("pgg-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
    private static Formula EqTo(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.Equal, right);
    private static Formula Logic(Formula left, FormulaLogicOperator op, Formula right) =>
        new Formula.Logic(Parenthesized(left), op, Parenthesized(right));
    private static Formula All(Formula variable, Formula domain, Formula body) =>
        Seq(Forall, Sp, variable, Sp, Colon, Sp, domain, Comma, Sp, body);
    private static Formula Arrow(Formula left, Formula right) => Seq(left, Sp, To, Sp, right);
    private static Formula FinOf(Formula n) => Call("Fin", n);
    private static Formula NumberSet(string name) => Seq(Mathbb, Grp(F.Id(name)));
    private static Formula Family(Formula size, Formula range) => Arrow(FinOf(size), range);
    private static Formula MatrixType(Formula q) => Call("Matrix", FinOf(q), FinOf(q), NumberSet("R"));
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Power(Formula basis, Formula exponent) =>
        new Formula.Power(basis, exponent);
    private static Formula IndexedSum(Formula variable, Formula domain, Formula term) =>
        Seq(Sum, Underscore, Grp(variable, Colon, domain), Sp, term);
    private static Formula LambdaOf(Formula variable, Formula body) => Seq(variable, Mapsto, body);
    private static Formula Even(Formula rho, Formula vector) => Call("evenIndex", rho, vector);
    private static Formula ParityType(Formula n, Formula l) =>
        Seq(Parenthesized(Family(n, NumberSet("Z"))), Sp, To, Plus, Sp,
            Parenthesized(Family(l, Call("ZMod", D(2)))));

    private static Formula PolynomialFormula()
    {
        Formula n = F.Id("n"), q = F.Id("q"), a = F.Id("A"), x = F.Id("x"), j = F.Id("j");
        Formula matrix = IndexedSum(j, FinOf(n), Call("smul", App(x, j), App(a, j)));
        return Disp(All(n, NumberSet("N"), All(q, NumberSet("N"),
            All(a, Family(n, MatrixType(q)), All(x, Family(n, NumberSet("R")),
                EqTo(Call("P", a, x), Call("det", matrix)))))));
    }

    private static Formula ParityFormula()
    {
        Formula n = F.Id("n"), l = F.Id("L"), a = F.Id("a"), j = F.Id("j");
        Formula cast = LambdaOf(j, Call("castInt", App(a, j)));
        return Disp(All(n, NumberSet("N"), All(l, NumberSet("N"),
            All(Rho, ParityType(n, l), All(a, Family(n, NumberSet("N")),
                Logic(Even(Rho, a), FormulaLogicOperator.Iff, EqTo(App(Rho, cast), D(0))))))));
    }

    private static Formula SumFormula()
    {
        Formula n = F.Id("n"), q = F.Id("q"), l = F.Id("L"), m = F.Id("m"),
            a = F.Id("A"), v = F.Id("V"), u = F.Id("u"), eta = F.Id("eta"),
            i = F.Id("i"), j = F.Id("j");
        Formula ai = Call("val", App(Alpha, i)), bi = Sub(D(1), ai);
        Formula av = LambdaOf(i, ai), bv = LambdaOf(i, bi);
        Formula indicator = Call("indicator", Even(Rho, Call("vecMul", av, v)));
        Formula sign = Seq(Prod, Underscore, Grp(i, Colon, FinOf(m)), Sp,
            Power(Call("castReal", App(Varepsilon, i)), bi));
        Formula Point(Formula vector) => LambdaOf(j,
            Call("castReal", Add(App(u, j), App(Call("vecMul", vector, v), j))));
        Formula Root(Formula vector) => Power(Call("P", a, Point(vector)), new Formula.Negate(eta));
        Formula term = Mul(Mul(Mul(indicator, Parenthesized(sign)), Root(av)), Root(bv));
        Formula formula = EqTo(Call("pggSum", a, Rho, v, Varepsilon, u, eta),
            IndexedSum(Alpha, Family(m, FinOf(D(2))), Parenthesized(term)));
        return Disp(All(n, NumberSet("N"), All(q, NumberSet("N"), All(l, NumberSet("N"),
            All(m, NumberSet("N"), All(a, Family(n, MatrixType(q)), All(Rho, ParityType(n, l),
                All(v, Family(m, Family(n, NumberSet("N"))),
                    All(Varepsilon, Family(m, NumberSet("Z")), All(u, Family(n, NumberSet("N")),
                        All(eta, NumberSet("R"), formula)))))))))));
    }

    private static Formula ClaimFormula()
    {
        Formula eta = F.Id("eta"), n = F.Id("n"), q = F.Id("q"), l = F.Id("L"),
            a = F.Id("A"), m = F.Id("m"), v = F.Id("V"), u = F.Id("u"),
            i = F.Id("i"), j = F.Id("j");
        Formula Imp(Formula p, Formula conclusion) => Logic(p, FormulaLogicOperator.Implies, conclusion);
        Formula signs = All(i, FinOf(m), Logic(EqTo(App(Varepsilon, i), D(1)),
            FormulaLogicOperator.Or, EqTo(App(Varepsilon, i), new Formula.Negate(D(1)))));
        Formula padding = All(j, FinOf(n), Rel(D(0), FormulaRelationOperator.LessThan, App(u, j)));
        Formula sumEven = Even(Rho, Call("vecMul", Call("const", FinOf(m), D(1)), v));
        Formula nonnegative = Rel(D(0), FormulaRelationOperator.LessThanOrEqual,
            Call("pggSum", a, Rho, v, Varepsilon, u, eta));
        Formula inner = Imp(sumEven, Imp(signs, Imp(padding, Imp(Even(Rho, u), nonnegative))));
        Formula configurations = All(m, NumberSet("N"),
            All(v, Family(m, Family(n, NumberSet("N"))),
                All(Varepsilon, Family(m, NumberSet("Z")), All(u, Family(n, NumberSet("N")), inner))));
        Formula psd = All(j, FinOf(n), Call("PosSemidef", App(a, j)));
        Formula pd = Call("PosDef", IndexedSum(j, FinOf(n), App(a, j)));
        Formula matrices = Imp(Rel(D(0), FormulaRelationOperator.LessThan, q),
            Imp(psd, Imp(pd, configurations)));
        Formula quantifiers = All(n, NumberSet("N"), All(q, NumberSet("N"), All(l, NumberSet("N"),
            All(a, Family(n, MatrixType(q)), All(Rho, ParityType(n, l), matrices)))));
        return Disp(Logic(F.Id("claim"), FormulaLogicOperator.Iff,
            All(eta, NumberSet("R"), Imp(Rel(D(0), FormulaRelationOperator.LessThan, eta), quantifiers))));
    }
}
