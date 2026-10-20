using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class BargmannImaginaryMaximizersDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Information/BargmannImaginaryMaximizers.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumContext/zhangxie2026bargmann");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every n at least three, the unit qubit tuples with imaginary Bargmann invariant tau n form one unitary orbit of a latitude polygon, allowing an independent phase at each vertex.",
        H("All qubit maximizers of the imaginary Bargmann invariant"),
        Blocks(
            Paragraph(Text("Vectors have type Fin 2 → ℂ. For a unit vector v, Matrix.vecMulVec v (star v) is its rank-one projector. Indices have type Fin n and start at zero. List.ofFn lists the outer products in increasing index order and List.prod takes their ordered matrix product. Real division, the real square root and natural powers have Lean's total meanings; the exponent n − 1 is natural subtraction, whereas the denominator 2 · (n − 1) uses real subtraction after coercing n to ℝ.")),
            Node("bargmann", "Ordered trace of pure states", BargmannFormula(),
                "Zhang and Xie, Definition 3.1, p. 9: “The so-called nth-order Bargmann invariant for such n-tuple Ψ = (ρ₁, …, ρₙ) is defined as Δₙ(Ψ) := Tr(ρ₁ ⋯ ρₙ).” Section 2, p. 4: “Unit vector |ψ⟩ in ℂ^d will be called wave functions and its ranked-one projector ψ ≡ |ψ⟩⟨ψ| will be called pure state.” Here d = 2 and each ρ is the displayed outer product of its amplitude vector with its conjugate.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("tau", "The maximal imaginary value", TauFormula(),
                "Zhang and Xie, Corollary 5.5, p. 25, Eq. (5.15): “τₙ := cosⁿ(π/n) secⁿ⁻¹(π/[2(n−1)]).” The reciprocal cosine power expresses the secant power; the classification below concerns n ≥ 3.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("maximizer", "The latitude polygon", MaximizerFormula(),
                "The jth vector is (√(1 − t), √t · exp(2πij/n)), with t = (1 − tan(π/[2(n−1)])/tan(π/n))/2. The square roots are embedded from ℝ into ℂ. For n ≥ 3 the weight t lies strictly between zero and one half. The last coordinate uses the complex coercions of j and n.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("claim", "The complete set of maximizing tuples", Disp(Equal(Named("claim"), Parenthesized(ClaimBody()))),
                "Zhang and Xie, p. 26: “The quantity τ_n predicts the upper bound for the imaginary part of any nth-order Bargmann invariant. This immediately raises the question: what is the complete set of n-tuples Ψ = (|ψ_1⟩, …, |ψ_n⟩) in ℂ² that achieve Im Tr(ψ_1 … ψ_n) = τ_n? We leave this characterization, along with the operational interpretation of the condition z ∈ 𝓑_{n+1} ∖ 𝓑_n, as interesting open problems for future work.” The displayed answer uses one common matrix U in Matrix.unitaryGroup and independent complex phases eta of norm one. The wave-function premise is star (Ψ j) dotProduct (Ψ j) = 1. The second question is outside this equivalence.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("result", "Classification of every maximizing qubit tuple", Disp(ClaimBody()),
                "Rephase consecutive overlaps onto one ray. AM–GM compares their product with their mean, and the exposed edge of the regular polygon of Fourier phases bounds that mean. Equality at the unique scalar maximum removes every Fourier mode except zero and one. Parseval's energy identity and unit length at two vertices force these two modes to be orthogonal. Their Gram matrix determines a common unitary, and the mean overlap fixes the latitude weight. Conversely, the polygon has constant consecutive overlap and its ordered trace has imaginary part tau n; unitary transformations and the individual phases preserve that trace.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("zhang-xie-2026-bargmann-imaginary-maximizers"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("bargmannmax-" + name), DeclarationHandle.Create(Module + name),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, openProblemResolutionClaim: resolution);

    private static Formula BargmannFormula()
    {
        Formula n = X("n"), j = X("j"), v = At(Psi, j);
        return Disp(All(n, Naturals(), All(Psi, Arrow(Fin(n), Vectors()),
            Equal(Call("bargmann", Psi), Call("Matrix.trace", Call("List.prod",
                Call("List.ofFn", LambdaOf(j, Fin(n), Call("Matrix.vecMulVec", v, Call("star", v))))))))));
    }

    private static Formula TauFormula()
    {
        Formula n = X("n"), nr = Typed(n, Reals());
        return Disp(All(n, Naturals(), Equal(Call("tau", n), Fraction(
            Power(Call("Real.cos", Fraction(Named("Real.pi"), nr)), n),
            Power(Call("Real.cos", Fraction(Named("Real.pi"),
                Multiply(D(2), Parenthesized(Subtract(nr, D(1)))))),
                Parenthesized(Subtract(n, D(1))))))));
    }

    private static Formula MaximizerFormula()
    {
        Formula n = X("n"), j = X("j"), t = X("t"), nr = Typed(n, Reals());
        Formula weight = Fraction(Subtract(D(1), Fraction(
            Call("Real.tan", Fraction(Named("Real.pi"), Multiply(D(2), Parenthesized(Subtract(nr, D(1)))))),
            Call("Real.tan", Fraction(Named("Real.pi"), nr)))), D(2));
        Formula phase = Call("Complex.exp", Fraction(
            Multiply(Multiply(Multiply(D(2), Typed(Named("Real.pi"), Complexes())), Named("Complex.I")), Typed(Call("val", j), Complexes())),
            Typed(n, Complexes())));
        Formula vector = Seq(Bang, OpenBracket, Typed(Call("Real.sqrt", Subtract(D(1), t)), Complexes()),
            Comma, Sp, Multiply(Typed(Call("Real.sqrt", t), Complexes()), phase), CloseBracket);
        return Disp(All(n, Naturals(), All(j, Fin(n), Seq(Named("let"), Sp,
            Typed(t, Reals()), Sp, Colon, Eq, Sp, weight, Semi, Sp,
            Equal(Call("maximizer", n, j), vector)))));
    }

    private static Formula ClaimBody()
    {
        Formula n = X("n"), j = X("j"), eta = X("eta"), u = X("U");
        Formula wave = All(j, Fin(n), Equal(Call("dotProduct", Call("star", At(Psi, j)), At(Psi, j)), D(1)));
        Formula phases = All(j, Fin(n), Equal(new Formula.Norm(At(eta, j)), D(1)));
        Formula tuple = All(j, Fin(n), Equal(At(Psi, j), Call("SMul.smul", At(eta, j),
            Call("Matrix.mulVec", u, Call("maximizer", n, j)))));
        Formula orbit = Some(u, Call("Matrix", Fin(D(2)), Fin(D(2)), Complexes()),
            And(new Formula.Relation(u, FormulaRelationOperator.MemberOf, Call("Matrix.unitaryGroup", Fin(D(2)), Complexes())),
                Some(eta, Arrow(Fin(n), Complexes()), And(phases, tuple))));
        return All(n, Naturals(), Imp(new Formula.Relation(D(3), FormulaRelationOperator.LessThanOrEqual, n),
            All(Psi, Arrow(Fin(n), Vectors()), Imp(wave,
                IffOf(Equal(Call("Complex.im", Call("bargmann", Psi)), Call("tau", n)), orbit)))));
    }

    private static Formula X(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname,
        Grp(name.Split('.').SelectMany((part, index) => index == 0
            ? new Formula[] { F.Id(part) } : new Formula[] { Dot, F.Id(part) }).ToArray()));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula At(Formula f, Formula arg) => new Formula.Apply(f, [arg]);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Sp, Colon, Sp, type));
    private static Formula Arrow(Formula a, Formula b) => Seq(Parenthesized(a), Sp, To, Sp, Parenthesized(b));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Vectors() => Arrow(Fin(D(2)), Complexes());
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Fraction(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Power(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Multiply(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Subtract(Formula a, Formula b) => Seq(a, Sp, Minus, Sp, b);
    private static Formula All(Formula x, Formula type, Formula body) => Seq(Forall, Sp, Typed(x, type), Comma, Sp, body);
    private static Formula Some(Formula x, Formula type, Formula body) => Seq(Exists, Sp, Typed(x, type), Comma, Sp, body);
    private static Formula LambdaOf(Formula x, Formula type, Formula body) => Seq(Named("fun"), Sp, Typed(x, type), Sp, Mapsto, Sp, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula IffOf(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
}
