using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class BeraSarbickiChruscinskiOptimizedMapsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/QuantumChannels/BeraSarbickiChruscinskiOptimizedMaps.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumContext/berasarbickichruscinski2023optimizedmaps");
    private const string Quote = "Conjecture 2. If GCD(n, k) = 3, then for the optimized map τ^{λ,α,β}_{n,k} = τ_{n,k} − λ_{|v⟩} H_{|v⟩} where |v⟩ = α|v₁⟩ + β|v₂⟩ one has λ^max_{|v⟩} ∈ [n − k, n − k + (n−3)/(n − ⅔k)]. Moreover, λ^max_{|v⟩} = n − k if α = 0 or β = 0, (12) λ^max_{|v⟩} = n − k + (n−3)/(n − ⅔k) if |α| = |β|. (13)";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An exact positive-input certificate refutes the gcd-three equator formula.",
        H("The gcd-three equator formula fails at dimension six"),
        Blocks(
            Node("tau", "The positive-map family", TauFormula(),
                "Page 1, Eq. (3): “τ_{n,k}(X) = (n − k)ε(X) + Σ_{i=1}^{k} ε(Sⁱ X S^{†i}) − X”. Page 2, Eq. (4): “ε(X) = Σ_{i=0}^{n−1} Tr[X eᵢᵢ] eᵢᵢ.” In standard coordinates ε is the composition of diagonalLinearMap and diagLinearMap. Page 2, Eq. (5): “S eᵢ = eᵢ₊₁ (mod n)”. Indices are Fin n, and addition of matrix indices is modular addition. The matrix S is displayed by its entries. The composition of mulLeft and mulRight sends X to Sⁱ X (Sⁱ)ᴴ. The sum is indexed by Finset.Icc 1 k.", AssessedProvenance.FromLiterature(Source)),
            Node("hadamardMap", "The rank-one Hadamard map", HadamardFormula(),
                "Page 2, Eq. (6): “H_{|v⟩}(X) = P_{|v⟩} ∘ X”, where “P_{|v⟩} = |v⟩⟨v|” and ∘ denotes the Hadamard product. vecMulVec v (star v) is the rank-one matrix with entries vᵢ conjugate(vⱼ). The displayed equality specifies the complex linear map on every matrix X.", AssessedProvenance.FromLiterature(Source)),
            Node("vr", "The two Fourier vectors", VectorFormula(),
                "Page 3, Eqs. (10)–(11): “|v₁⟩ = (1/√n)(1, ω^{n/3}, (ω^{n/3})² …, (ω^{n/3})^{n−1})ᵀ” and “|v₂⟩ = (1/√n)(1, ω^{2n/3}, (ω^{2n/3})² …, (ω^{2n/3})^{n−1})ᵀ”. Here ω = e^{2πi/n}. The coordinate expression exp(2πi r j/3)/√n is used for r = 1, 2. All divisions in this expression take place in ℂ; j is first read as a natural-number coordinate.", AssessedProvenance.FromLiterature(Source)),
            Node("IsLambdaMax", "The greatest positivity parameter", LambdaFormula(),
                "Page 2: “Let λ^max_{|v⟩} be the largest value of λ_{|v⟩}, such that the map τ_{n,k} − λ_{|v⟩} H_{|v⟩} is positive.” IsGreatest expresses attainment and maximality among nonnegative real parameters. IsPositive is FiniteKrausChannel.PhyslibLeaf.MatrixMap.IsPositive: every positive semidefinite input has a positive semidefinite output.", AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Conjecture 2, Eq. (13)",
                Seq(F.Id("claim"), Sp, Iff, Sp, Parenthesized(ClaimBody())),
                "Page 3: “" + Quote + "” The proposition selects Eq. (13) alone. The source range k = 1, …, n − 1 is expressed by 1 ≤ k and k < n. The coefficients α and β are complex numbers a and b, with squared norms summing to one and equal norms. The vectors are j ↦ a·vr(n,1,j) + b·vr(n,2,j). The predicted parameter is a real expression; subtraction and division are in ℝ.", AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(DescribeId.Create("bsc-result"), DeclarationHandle.Create(Prefix + "result"),
                H("Refutation of the equator assertion"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Take n = 6, k = 3 and a = b = 1/√2. The asserted parameter is 15/4. For q = (1,0,0,1,0,0), the matrix R = I/60 + (27/60) vecMulVec(q,star(q)) is positive semidefinite. Its quadratic forms are q* tau(6,3)(R) q = 59/30 and q* hadamardMap(6,v)(R) q = 11/18. Their difference at 15/4 is −13/40. A positive semidefinite output has a nonnegative quadratic form at q, giving a contradiction. Only coordinates 0 and 3 of v enter this calculation. The argument does not determine the exact greatest positivity parameter or settle the other parts of Conjecture 2."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("bsc-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complex => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Qualified(string owner, string name) => Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula QCall(string owner, string name, params Formula[] args) => App(Qualified(owner, name), args);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Cast(Formula x, Formula type) => Parenthesized(Seq(x, Sp, Colon, Sp, type));
    private static Formula All(string v, Formula type, Formula body) => new Formula.BindMany(FormulaQuantifier.ForAll,
        [new Formula.BoundVariable(FormulaIdentifier.Create(v), type)], body);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Mul(Formula a, Formula b) => Multiply(a, b);
    private static Formula Pow(Formula a, long n) => new Formula.Power(a, Num(n));
    private static Formula FracOf(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Mat(Formula n) => Call("Matrix", Fin(n), Fin(n), Complex);
    private static Formula Vector(Formula n) => new Formula.TypeArrow(Fin(n), Complex);
    private static Formula Comp(Formula a, Formula b) => QCall("LinearMap", "comp", a, b);
    private static Formula Smul(Formula a, Formula b) => Seq(a, Sp, Cdot, Sp, Parenthesized(b));
    private static Formula Nonzero(Formula n, Formula body) => Seq(OpenBracket, Call("NeZero", n), CloseBracket, Sp, body);

    private static Formula TauFormula()
    {
        Formula n = F.Id("n"), k = F.Id("k"), i = F.Id("i"), s = F.Id("S");
        Formula matrix = QCall("Matrix", "of", Parenthesized(Seq(F.Id("fun"), Sp,
            F.Id("a"), Sp, F.Id("b"), Sp, Colon, Sp, Fin(n), Sp, Mapsto, Sp,
            F.Id("if"), Sp, F.Id("a"), Sp, Eq, Sp, F.Id("b"), Sp, Plus, Sp, Num(1), Sp,
            F.Id("then"), Sp, Num(1), Sp, F.Id("else"), Sp, Num(0))));
        Formula power = new Formula.Power(s, i);
        Formula conjugation = Comp(QCall("LinearMap", "mulLeft", Complex, power),
            QCall("LinearMap", "mulRight", Complex, Call("conjTranspose", power)));
        Formula projection = Comp(QCall("Matrix", "diagonalLinearMap", Fin(n), Complex, Complex),
            QCall("Matrix", "diagLinearMap", Fin(n), Complex, Complex));
        Formula summand = Comp(projection, conjugation);
        Formula sum = Seq(Sum, Underscore, Grp(i, Sp, InMacro, Sp, QCall("Finset", "Icc", Num(1), k)),
            Sp, Parenthesized(summand));
        Formula rhs = Subtract(Add(Smul(Parenthesized(Subtract(Cast(n, Complex), Cast(k, Complex))), projection), sum),
            Qualified("LinearMap", "id"));
        Formula let = Seq(F.Id("let"), Sp, s, Sp, Colon, Sp, Mat(n), Sp, Eq, Sp, matrix, Semi, Sp, rhs);
        return All("n", Nat, All("k", Nat, Nonzero(n, Eqn(Call("tau", n, k), Parenthesized(let)))));
    }

    private static Formula HadamardFormula()
    {
        Formula n = F.Id("n"), v = F.Id("v"), x = F.Id("X");
        Formula rhs = QCall("Matrix", "hadamard", QCall("Matrix", "vecMulVec", v, Call("star", v)), x);
        return All("n", Nat, All("v", Vector(n), All("X", Mat(n),
            Eqn(App(Call("hadamardMap", n, v), x), rhs))));
    }

    private static Formula VectorFormula()
    {
        Formula n = F.Id("n"), r = F.Id("r"), j = F.Id("j");
        Formula angle = FracOf(Mul(Mul(Mul(Mul(Num(2), Cast(Qualified("Real", "pi"), Complex)), Qualified("Complex", "I")),
            Cast(r, Complex)), Cast(Cast(j, Nat), Complex)), Num(3));
        Formula rhs = FracOf(QCall("Complex", "exp", angle), Cast(QCall("Real", "sqrt", Cast(n, Real)), Complex));
        return All("n", Nat, All("r", Nat, All("j", Fin(n), Eqn(Call("vr", n, r, j), rhs))));
    }

    private static Formula LambdaFormula()
    {
        Formula n = F.Id("n"), k = F.Id("k"), v = F.Id("v"), lam = F.Id("lam"), l = F.Id("l");
        Formula positive = Call("IsPositive", Parenthesized(Subtract(Call("tau", n, k), Smul(Cast(l, Complex), Call("hadamardMap", n, v)))));
        Formula set = Seq(OpenBrace, l, Sp, Colon, Sp, Real, Sp, Mid, Sp, And(Leq(Num(0), l), positive), CloseBrace);
        return All("n", Nat, All("k", Nat, Nonzero(n, All("v", Vector(n), All("lam", Real,
            Seq(Call("IsLambdaMax", n, k, v, lam), Sp, Iff, Sp, Parenthesized(Call("IsGreatest", set, lam))))))));
    }

    private static Formula ClaimBody()
    {
        Formula n = F.Id("n"), k = F.Id("k"), a = F.Id("a"), b = F.Id("b"), j = F.Id("j");
        Formula v = Parenthesized(Seq(F.Id("fun"), Sp, j, Sp, Colon, Sp, Fin(n), Sp, Mapsto, Sp,
            Add(Mul(a, Call("vr", n, Num(1), j)), Mul(b, Call("vr", n, Num(2), j)))));
        Formula parameter = Add(Subtract(Cast(n, Real), Cast(k, Real)),
            FracOf(Subtract(Cast(n, Real), Num(3)), Subtract(Cast(n, Real), Mul(FracOf(Num(2), Num(3)), Cast(k, Real)))));
        Formula body = Imp(Eqn(Add(Pow(new Formula.Norm(a), 2), Pow(new Formula.Norm(b), 2)), Num(1)),
            Imp(Eqn(new Formula.Norm(a), new Formula.Norm(b)), Call("IsLambdaMax", n, k, v, parameter)));
        return All("n", Nat, All("k", Nat, Nonzero(n, Imp(Leq(Num(1), k), Imp(Less(k, n),
            Imp(Eqn(QCall("Nat", "gcd", n, k), Num(3)), All("a", Complex, All("b", Complex, body))))))));
    }
}
