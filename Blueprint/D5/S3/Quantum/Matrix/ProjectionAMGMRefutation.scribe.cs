using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class ProjectionAMGMRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Matrix/ProjectionAMGMRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/sunluoye2020projectionamgm");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A rank-one projection family gives a negative quadratic form for the matrix AM-GM difference.",
        H("Projection-matrix AM-GM refutation"),
        Blocks(
            Entry("six-perms", "sixPerms", "The six permutations of three points", SixPerms(),
                "The identity, the three transpositions, and the two products of adjacent transpositions list all permutations of Fin 3.", true, AssessedProvenance.FromRepo()),
            Entry("six-perms-univ", "sixPerms_univ", "The list contains every permutation", Disp(Eq(V("sixPerms"),
                Parenthesized(Seq(Qualified("Finset", "univ"), Colon, Call("Finset", Call("Equiv.Perm", Fin(Num(3)))))))),
                "The finite set sixPerms equals the finite set of all permutations of Fin 3.", false, AssessedProvenance.FromRepo()),
            Entry("mean-proj", "meanProj", "Arithmetic mean of projections", MeanProj(),
                "meanProj scales the finite sum of a projection family by the inverse of its cardinality.", true, AssessedProvenance.FromLiterature(Source)),
            Entry("sym-prod", "symProd", "Symmetrized projection product", SymProd(),
                "symProd scales the sum over all permutation words by the inverse factorial; List.reverse makes the first permutation entry the rightmost factor.", true, AssessedProvenance.FromLiterature(Source)),
            Entry("matrix-amgm-claim", "claim", "Matrix AM-GM positive-semidefinite claim", Claim(),
                "Sun, Luo, and Ye state in Section 3.3: \"We observe that we only need to prove a matrix AM-GM inequality for projection matrices. We conjecture that the following matrix AM-GM inequality holds. Conjecture (matrix AM-GM inequality for projection matrices). Suppose Pᵢ ∈ ℝᴺˣᴺ, i=1,…,n are projection matrices, then (1/n!) Σ_{σ=(σ₁,…,σₙ)∈Γ} P_{σₙ} P_{σₙ₋₁} ⋯ P_{σ₁} ⪯ ((1/n) Σᵢ Pᵢ)ⁿ.\" Here Γ is the set of all permutations of {1,…,n}, and X ⪯ Y means that Y−X is positive semidefinite. The displayed formula is its real finite-dimensional encoding.", true, AssessedProvenance.FromLiterature(Source)),
            Entry("refutation", "result", "A negative quadratic form at dimension three", Disp(Seq(Neg, Sp, V("claim"))),
                "The explicit matrices on Fin 3 satisfy the projection hypotheses, but z=(1,1,1) gives zᵀ((meanProj P)^3−symProd P)z=−8/243. Positive semidefiniteness would force this quadratic form to be nonnegative, so the universal statement is false.", false, AssessedProvenance.FromRepo(Source), DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        string prose, bool definition, AssessedProvenance provenance, DescribeRole? role = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula),
            provenance,
            Blocks(Paragraph(Text(prose))), role ?? (definition ? DescribeRole.Definition : DescribeRole.Theorem),
            name == "result" ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("sun-luo-ye-2020-projection-matrix-amgm"),
                ResolutionKind.Refuted) : null);

    private static Formula SixPerms()
    {
        Formula Transposition(byte i, byte j) => Call("Equiv.swap",
            Parenthesized(Seq(D(i), Colon, Fin(Num(3)))), D(j));
        Formula s01 = Transposition(0, 1), s02 = Transposition(0, 2), s12 = Transposition(1, 2);
        Formula type = Call("Finset", Call("Equiv.Perm", Fin(Num(3))));
        return Disp(Eq(Parenthesized(Seq(V("sixPerms"), Colon, type)),
            new Formula.SetLiteral([Num(1), s01, s02, s12, Mul(s01, s12), Mul(s12, s01)])));
    }

    private static Formula MeanProj()
    {
        Formula n = V("n"), N = V("N"), p = V("P");
        Formula body = Smul(Call("Inv.inv", Cast(n)), Sum("i", Fin(n), App(p, V("i"))));
        return Disp(All("n", Nat(), All("N", Nat(),
            All("P", Arrow(Fin(n), Matrix(N)), Eq(Call("meanProj", p), body)))));
    }

    private static Formula SymProd()
    {
        Formula n = V("n"), N = V("N"), p = V("P"), sigma = V("sigma"), k = V("k");
        Formula word = Call("List.prod", Call("List.reverse",
            Call("List.ofFn", Lambda("k", Fin(n), App(p, App(sigma, k))))));
        Formula body = Smul(Call("Inv.inv", Cast(Call("Nat.factorial", n))),
            Sum("sigma", Call("Equiv.Perm", Fin(n)), word));
        return Disp(All("n", Nat(), All("N", Nat(),
            All("P", Arrow(Fin(n), Matrix(N)), Eq(Call("symProd", p), body)))));
    }

    private static Formula Claim()
    {
        Formula n = V("n"), N = V("N"), p = V("P"), i = V("i");
        Formula assumptions = Imp(Leq(Num(1), n),
            Imp(All("i", Fin(n), And(Eq(Call("Matrix.transpose", App(p, i)), App(p, i)),
                Eq(Mul(App(p, i), App(p, i)), App(p, i)))),
                Pos(Sub(Pow(Call("meanProj", p), n), Call("symProd", p)))));
        Formula quantified = All("n", Nat(), All("N", Nat(),
            All("P", Arrow(Fin(n), Matrix(N)), assumptions)));
        return Disp(Iff(V("claim"), quantified));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(V(name), Colon, type)), Comma, Sp, body);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Real() => Seq(Mathbb, Grp(V("R")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Matrix(Formula n) => Call("Matrix", Fin(n), Fin(n), Real());
    private static Formula Arrow(Formula a, Formula b) => Seq(a, To, Sp, b);
    private static Formula Cast(Formula x) => Parenthesized(Seq(x, Colon, Real()));
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(name.Contains('.') ? Qualified(name.Split('.')[0], name.Split('.')[1]) : V(name), [.. args]);
    private static Formula Qualified(string owner, string name) => Seq(Operatorname, Grp(V(owner), Dot, V(name)));
    private static Formula App(Formula f, Formula x) => Seq(f, Parenthesized(x));
    private static Formula Lambda(string name, Formula type, Formula body) =>
        Seq(F.Id("fun"), Sp, Parenthesized(Seq(V(name), Colon, type)), Sp, Mapsto, Sp, body);
    private static Formula Sum(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(F.Sum, Seq(V(name), Colon, type)), Sp, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Smul(Formula a, Formula b) => Seq(a, Cdot, Sp, Parenthesized(b));
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Parenthesized(a), b);
    private static Formula Pos(Formula a) => Call("Matrix.PosSemidef", a);
}
