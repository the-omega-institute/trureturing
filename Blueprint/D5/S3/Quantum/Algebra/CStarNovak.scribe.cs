using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class CStarNovakDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Algebra/CStarNovak.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/krishna2021cstarnovak");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three self-adjoint matrices in Matrix (Fin 2) (Fin 2) complex numbers refute Krishna's C*-algebraic Novak conjecture. Their differences have scalar squares, and the exponential series gives cosine values 1, 1 and -1. The associated left-linear quadratic form takes the value -2 times the identity.",
        H("A matrix refutation of the C*-algebraic Novak conjecture"),
        Blocks(
            Node("ncos", "C*-algebraic cosine", CosineFormula(),
                "Definition 4.1 (arXiv:2108.06662v1, p. 9): “Define the C*-algebraic cosine function by cos: 𝒜 ∋ x ↦ cos x ≔ (eⁱˣ + e⁻ⁱˣ)/2 ∈ 𝒜.” Here ncos uses NormedSpace.exp, the exponential power series ∑ xⁿ/n!. Multiplication by the complex inverse of 2 is scalar multiplication; this definition also makes sense on a complex normed algebra before imposing completeness.",
                "ncos", AssessedProvenance.FromLiterature(Source)),
            Node("entry", "Ordered cosine-product entries", EntryFormula(),
                "The entry in Conjecture 4.3 (p. 10) is ∏_{l=1}^{d} (1+cos (x_{j,l}-x_{k,l}))/2-1/n. List.ofFn enumerates Fin d in increasing order, and List.prod preserves that order. Fin n and Fin d correspond to the source's indices by adding one. The subtraction uses (n : ℂ)⁻¹ acting on the algebra identity; each centered difference uses ncos.",
                "novakEntry", AssessedProvenance.FromLiterature(Source)),
            Node("positive", "The source's matrix positivity", PositiveFormula(),
                "Section 2 (p. 4): “Similar to the scalar case, A ≔ [a_{j,k}]_{1≤j,k≤n} ∈ Mₙ(𝒜) is said to be positive if it is self-adjoint and ⟨Ax, x⟩ ≥ 0, ∀ x ∈ 𝒜ⁿ, where ≥ is the partial order on the set of all positive elements of 𝒜.” The entrywise star-transpose condition encodes self-adjointness. The double sum is exactly the left-linear Hilbert-module form ⟨Mv,v⟩ = ∑ⱼ∑ₖ Mⱼₖ vₖ star(vⱼ). A centered dot denotes scalar multiplication and juxtaposition denotes algebra multiplication.",
                "IsPositiveMatrix", AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Conjecture 4.3", ClaimFormula(),
                "Conjecture 4.3 (C*-algebraic Novak's conjecture, p. 10): “Let 𝒜 be a unital C*-algebra. Then the matrix [∏_{l=1}^{d} (1+cos (x_{j,l}-x_{k,l}))/2-1/n]_{1≤j,k≤n} is positive for all n,d≥2 and all choices of x_j=(x_{j,1}, …, x_{j,d})∈𝒜_saᵈ, ∀1≤j≤n.” The encoding quantifies A : Type with CStarAlgebra, PartialOrder and StarOrderedRing. Mathlib's CStarAlgebra is unital. The restriction to Type weakens the source's universe range, so negating this restricted claim refutes the source statement. The displayed brackets are anonymous Lean instance arguments.",
                "claim", AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(DescribeId.Create("novak-result"), DeclarationHandle.Create(Prefix + "result"),
                H("Refutation in two by two complex matrices"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Named("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Take n = 3, d = 2 and x j l = A j, with A₁ = 3πI, A₂ = π diag(5,1), and A₃ = (π/4)[[19,√15],[√15,5]]. These are self-adjoint. The three off-diagonal squared differences are 4π²I, 4π²I and π²I. Pairing the exponential-series terms into even and odd powers shows that a scalar square X² = c²I gives ncos X = cos(c)I. Thus the three cosines are I, I and -I, every factor is I or zero, and the matrix is (1/3)[[2,2,2],[2,2,-1],[2,-1,2]] with every entry multiplied by I. At v = (-2,1,1)I its quadratic form is -2I, which is not nonnegative in the matrix positive-semidefinite order. Theorem 4.4 of the source proves the commutative case; this refutation leaves that theorem unaffected."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("krishna-2021-cstar-novak-conjecture"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string id, string title, Formula formula,
        string prose, string declaration, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("novak-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Apply(Formula head, params Formula[] args) => new Formula.Apply(head, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Instances(Formula body, params Formula[] types) =>
        Seq([.. types.Select(type => Seq(OpenBracket, type, CloseBracket, Sp)), body]);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula N() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula C() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Fin(Formula size) => Call("Fin", size);
    private static Formula Arrow(Formula from, Formula to) => new Formula.TypeArrow(from, to);
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Inverse(Formula value) => new Formula.Power(value, Seq(Minus, D(1)));
    private static Formula Smul(Formula scalar, Formula value) => Seq(scalar, Sp, Cdot, Sp, Parenthesized(value));
    private static Formula SumOver(string name, Formula type, Formula term) =>
        Seq(Sum, Underscore, Grp(Seq(F.Id(name), Colon, Sp, type)), Sp, term);

    private static Formula CosineFormula()
    {
        Formula a = F.Id("A"), x = F.Id("x");
        Formula ix = Smul(Qualified("Complex", "I"), x);
        Formula sum = Seq(Apply(Qualified("NormedSpace", "exp"), ix), Sp, Plus, Sp,
            Apply(Qualified("NormedSpace", "exp"), Seq(Minus, Parenthesized(ix))));
        return Disp(All("A", Seq(Named("Type"), Star), Instances(All("x", a,
            Equal(Call("ncos", x), Smul(Inverse(Cast(D(2), C())), sum))),
            Call("NormedRing", a), Call("NormedAlgebra", C(), a))));
    }

    private static Formula EntryFormula()
    {
        Formula a = F.Id("A"), n = F.Id("n"), d = F.Id("d"), x = F.Id("x");
        Formula j = F.Id("j"), k = F.Id("k"), l = F.Id("l");
        Formula difference = Seq(Apply(x, j, l), Sp, Minus, Sp, Apply(x, k, l));
        Formula factor = Smul(Inverse(Cast(D(2), C())), Seq(D(1), Sp, Plus, Sp, Call("ncos", difference)));
        Formula lambda = Parenthesized(Seq(Named("fun"), Sp, Cast(l, Fin(d)), Sp, Mapsto, Sp, factor));
        Formula product = Apply(Qualified("List", "prod"), Apply(Qualified("List", "ofFn"), lambda));
        Formula equation = Equal(Call("novakEntry", n, d, x, j, k), Seq(product, Sp, Minus, Sp,
            Smul(Inverse(Cast(n, C())), Cast(D(1), a))));
        return Disp(All("A", Seq(Named("Type"), Star), Instances(All("n", N(), All("d", N(),
            All("x", Arrow(Fin(n), Arrow(Fin(d), a)), All("j", Fin(n), All("k", Fin(n), equation))))),
            Call("CStarAlgebra", a))));
    }

    private static Formula PositiveFormula()
    {
        Formula a = F.Id("A"), n = F.Id("n"), m = F.Id("M"), v = F.Id("v");
        Formula j = F.Id("j"), k = F.Id("k");
        Formula hermitian = All("j", Fin(n), All("k", Fin(n),
            Equal(Call("star", Apply(m, j, k)), Apply(m, k, j))));
        Formula summand = Seq(Apply(m, j, k), Sp, Apply(v, k), Sp, Call("star", Apply(v, j)));
        Formula positive = All("v", Arrow(Fin(n), a),
            Le(D(0), SumOver("j", Fin(n), SumOver("k", Fin(n), summand))));
        return Disp(All("A", Seq(Named("Type"), Star), Instances(All("n", N(),
            All("M", Arrow(Fin(n), Arrow(Fin(n), a)), Iff(Call("IsPositiveMatrix", m), And(hermitian, positive)))),
            Call("CStarAlgebra", a), Call("PartialOrder", a))));
    }

    private static Formula ClaimFormula()
    {
        Formula a = F.Id("A"), n = F.Id("n"), d = F.Id("d"), x = F.Id("x");
        Formula j = F.Id("j"), k = F.Id("k"), l = F.Id("l"), v = F.Id("v");
        Formula Entry(Formula row, Formula column)
        {
            Formula difference = Seq(Apply(x, row, l), Sp, Minus, Sp, Apply(x, column, l));
            Formula ix = Smul(Qualified("Complex", "I"), difference);
            Formula cosine = Smul(Inverse(Cast(D(2), C())),
                Seq(Apply(Qualified("NormedSpace", "exp"), ix), Sp, Plus, Sp,
                    Apply(Qualified("NormedSpace", "exp"), Seq(Minus, Parenthesized(ix)))));
            Formula factor = Smul(Inverse(Cast(D(2), C())), Seq(D(1), Sp, Plus, Sp, cosine));
            Formula lambda = Parenthesized(Seq(Named("fun"), Sp, Cast(l, Fin(d)), Sp, Mapsto, Sp, factor));
            Formula product = Apply(Qualified("List", "prod"), Apply(Qualified("List", "ofFn"), lambda));
            return Seq(product, Sp, Minus, Sp, Smul(Inverse(Cast(n, C())), Cast(D(1), a)));
        }
        Formula selfAdjoint = All("j", Fin(n), All("l", Fin(d),
            Call("IsSelfAdjoint", Apply(x, j, l))));
        Formula hermitian = All("j", Fin(n), All("k", Fin(n),
            Equal(Call("star", Entry(j, k)), Entry(k, j))));
        Formula summand = Seq(Parenthesized(Entry(j, k)), Sp, Apply(v, k), Sp, Call("star", Apply(v, j)));
        Formula positive = All("v", Arrow(Fin(n), a),
            Le(D(0), SumOver("j", Fin(n), SumOver("k", Fin(n), summand))));
        Formula body = All("n", N(), All("d", N(), Imp(Le(D(2), n), Imp(Le(D(2), d),
            All("x", Arrow(Fin(n), Arrow(Fin(d), a)), Imp(selfAdjoint, And(hermitian, positive)))))));
        return Disp(Iff(Named("claim"), All("A", Named("Type"), Instances(body,
            Call("CStarAlgebra", a), Call("PartialOrder", a), Call("StarOrderedRing", a)))));
    }
}
