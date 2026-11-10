using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.FiniteGeometry.Polytopes;

internal sealed class JohnsonPaparellaHadamardPolyhedraRefutationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S0/FiniteGeometry/Polytopes/JohnsonPaparellaHadamardPolyhedraRefutation";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/FiniteGeometry/johnsonpaparella2025perron");
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complex => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula App(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, variable, Colon, Sp, type, Comma, Sp, body);
    private static Formula Some(Formula variable, Formula type, Formula body) =>
        Seq(Exists, Sp, variable, Colon, Sp, type, Comma, Sp, body);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Vectors(Formula n) => new Formula.TypeArrow(Fin(n), Complex);
    private static Formula Sets(Formula n) => Call("Set", Vectors(n));
    private static Formula Matrices(Formula n) => Call("Matrix", Fin(n), Fin(n), Complex);
    private static Formula SetOf(Formula variable, Formula type, Formula body) =>
        Seq(OpenBrace, variable, Colon, Sp, type, Mid, Sp, body, CloseBrace);
    private static Formula Conjunction(Formula left, Formula right) =>
        Seq(Parenthesized(left), Land, Sp, Parenthesized(right));
    private static Formula MatrixBody(Formula s, Formula x) =>
        Parenthesized(Seq(s, Cdot, Sp, App(Qualified("Matrix", "diagonal"), x), Cdot, Sp,
            new Formula.Power(s, Seq(Minus, D(1)))));
    private static Formula Closure(Formula n, Formula k)
    {
        var x = F.Id("x"); var y = F.Id("y");
        return All(x, Vectors(n), All(y, Vectors(n), Seq(x, InMacro, Sp, k, Implies, Sp,
            y, InMacro, Sp, k, Implies, Sp, x, Cdot, Sp, y, InMacro, Sp, k)));
    }
    private static Formula HalfSpaceFormula()
    {
        var n = F.Id("n"); var a = F.Id("a"); var b = F.Id("b");
        var x = F.Id("x"); var i = F.Id("i");
        var sum = Seq(new Formula.Subscript(Sum, Seq(i, Colon, Sp, Fin(n))),
            Call("star", Call("a", i)), Cdot, Sp, Call("x", i));
        return All(n, Nat, All(a, Vectors(n), All(b, Real,
            Seq(Call("halfSpace", a, b), Eq, SetOf(x, Vectors(n),
                Seq(b, Leq, Sp, App(Qualified("Complex", "re"), Parenthesized(sum))))))));
    }
    private static Formula PolyhedronFormula(bool homogeneous)
    {
        var n = F.Id("n"); var k = F.Id("K"); var m = F.Id("m");
        var a = F.Id("a"); var b = F.Id("b"); var j = F.Id("j"); var x = F.Id("x");
        var offsets = homogeneous ? D(0) : Call("b", j);
        var normals = All(j, Fin(m), Seq(Call("a", j), Neq, Sp, D(0)));
        var intersection = Seq(k, Eq, SetOf(x, Vectors(n),
            All(j, Fin(m), Seq(x, InMacro, Sp, Call("halfSpace", Call("a", j), offsets)))));
        var body = Conjunction(normals, intersection);
        var family = homogeneous ? body : Some(b, new Formula.TypeArrow(Fin(m), Real), body);
        return All(n, Nat, All(k, Sets(n), Seq(
            Call(homogeneous ? "IsSourcePolyhedralCone" : "IsSourcePolyhedron", k), Iff, Sp,
            Some(m, Nat, Conjunction(Seq(D(0), Lt, m),
                Some(a, new Formula.TypeArrow(Fin(m), Vectors(n)), family))))));
    }
    private static Formula PolytopeFormula()
    {
        var n = F.Id("n"); var k = F.Id("K");
        return All(n, Nat, All(k, Sets(n), Seq(Call("IsSourcePolytope", k), Iff, Sp,
            Conjunction(Call("IsSourcePolyhedron", k), App(Qualified("Bornology", "IsBounded"), k)))));
    }
    private static Formula SpectraconeFormula()
    {
        var n = F.Id("n"); var s = F.Id("S"); var x = F.Id("x");
        var i = F.Id("i"); var j = F.Id("j");
        return All(n, Nat, All(s, Matrices(n), Seq(Call("spectracone", s), Eq,
            SetOf(x, Vectors(n), All(i, Fin(n), All(j, Fin(n),
                Seq(Parenthesized(Seq(D(0), Colon, Sp, Complex)), Leq, Sp, App(MatrixBody(s, x), i, j))))))));
    }
    private static Formula SpectratopeFormula()
    {
        var n = F.Id("n"); var s = F.Id("S"); var x = F.Id("x");
        var one = Parenthesized(Seq(D(1), Colon, Sp, Vectors(n)));
        return All(n, Nat, All(s, Matrices(n), Seq(Call("spectratope", s), Eq,
            SetOf(x, Vectors(n), Conjunction(Seq(x, InMacro, Sp, Call("spectracone", s)),
                Seq(App(Qualified("Matrix", "mulVec"), MatrixBody(s, x), one), Eq, D(1)))))));
    }
    private static Formula Converse(Formula n, Formula k, bool cone)
    {
        var s = F.Id("S");
        return Seq(Call(cone ? "IsSourcePolyhedralCone" : "IsSourcePolytope", k), Implies, Sp,
            Parenthesized(Closure(n, k)), Implies, Sp, Some(s, Matrices(n),
                Conjunction(Seq(App(Qualified("Matrix", "det"), s), Neq, Sp, D(0)),
                    Seq(k, Eq, Call(cone ? "spectracone" : "spectratope", s)))));
    }
    private static Formula ClaimBody()
    {
        var n = F.Id("n"); var k = F.Id("K");
        return All(n, Nat, Seq(D(0), Lt, n, Implies, Sp, All(k, Sets(n),
            Conjunction(Converse(n, k, true), Converse(n, k, false)))));
    }
    private static DocumentBlock Node(string name, string title, Formula formula,
        AssessedProvenance provenance, string prose, DescribeRole role,
        OpenProblemResolutionClaim? resolutionClaim = null) =>
        Describe.Lean(DescribeId.Create(name.ToLowerInvariant()), DeclarationHandle.Create(Module + "." + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role, openProblemResolutionClaim: resolutionClaim);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hadamard closure does not imply exact spectracone representation.",
        H("A Hadamard-closed cone that is not a spectracone"), Blocks(
            Node("halfSpace", "Real half-spaces in complex coordinates", HalfSpaceFormula(), AssessedProvenance.FromLiterature(Source),
                "Page 5, Section 2.3: “If a ∈ ℂⁿ, a ≠ 0, and b ∈ ℝ, then” H(a,b) := {x ∈ ℂⁿ | Re(⟨a, x⟩) ≥ b} = {x ∈ ℂⁿ | Re(⟨x, a⟩) ≥ b} “is a closed half-space determined by the hyperplane {x ∈ ℂⁿ | Re(⟨x, a⟩) = b}.” The finite coordinates are Fin n, and the conjugate of a multiplies x in the displayed sum. Nonzero normals are required by the finite-intersection definitions below.", DescribeRole.Definition),
            Node("IsSourcePolyhedron", "Finite intersections of half-spaces", PolyhedronFormula(false), AssessedProvenance.FromLiterature(Source),
                "Page 5, Section 2.3: “Any set of the form” ⋂ₖ₌₁ᵐ H(aₖ,bₖ) = ⋂ₖ₌₁ᵐ {x ∈ ℂⁿ | Re(⟨aₖ, x⟩) ≥ bₖ} “is called a polyhedron and a bounded polyhedron is called a polytope.” The number m is positive, every normal is nonzero, and each member of Fin m supplies one inequality.", DescribeRole.Definition),
            Node("IsSourcePolytope", "Bounded polyhedra", PolytopeFormula(), AssessedProvenance.FromLiterature(Source),
                "Page 5, Section 2.3: “is called a polyhedron and a bounded polyhedron is called a polytope.” Boundedness is Bornology.IsBounded for the usual metric on the finite complex function space.", DescribeRole.Definition),
            Node("IsSourcePolyhedralCone", "Homogeneous half-spaces", PolyhedronFormula(true), AssessedProvenance.FromLiterature(Source),
                "Page 5, Section 2.3: “Any set of the form” ⋂ₖ₌₁ᵐ H(aₖ) = {x ∈ ℂⁿ | Re(⟨aₖ, x⟩) ≥ 0} “is called a polyhedral cone.” The finite intersection requires every index k; H(a) means H(a,0). All half-spaces are real, including those that impose imaginary-coordinate equalities.", DescribeRole.Definition),
            Node("spectracone", "The spectracone of a matrix", SpectraconeFormula(), AssessedProvenance.FromLiterature(Source),
                "Page 10, Definition 4.1: “If S ∈ GLₙ(ℂ), then:” “𝒞(S) := {x ∈ ℂⁿ | Mₓ := SDₓS⁻¹ ≥ 0} is called the (Perron) spectracone of S;”. Matrix.diagonal x is Dₓ. The complex order requires both a nonnegative real part and zero imaginary part in every entry. The formula defines the set for every square S; invertibility is required in the representation assertion.", DescribeRole.Definition),
            Node("spectratope", "The stochastic cross-section", SpectratopeFormula(), AssessedProvenance.FromLiterature(Source),
                "Page 10, Definition 4.1: “𝒫(S) := {x ∈ 𝒞(S) | Mₓe = e} is called the (Perron) spectratope of S;”. The function 1 is the all-ones vector e, and Matrix.mulVec expresses the row-sum equation.", DescribeRole.Definition),
            Node("claim", "Question 9.1", Seq(Named("claim"), Iff, Sp, Parenthesized(ClaimBody())), AssessedProvenance.FromLiterature(Source),
                "Page 27, Question 9.1: “If K is a polyhedral cone (polytope) that is closed with respect to the Hadamard product, is there an invertible matrix S such that K = 𝒞(S) (K = 𝒫(S))?” The proposition asks both converses for every positive n and every subset of Fin n → ℂ. Vector multiplication is coordinatewise. The diagonalizer has the same size n; no identity, dimension, pointedness or spectral-admissibility condition is added.", DescribeRole.Definition),
            Node("result", "A negative answer to Question 9.1", Seq(Neg, Sp, Parenthesized(ClaimBody())), AssessedProvenance.FromRepo(Source),
                "The explicit m = 10 cone in three coordinates has fourteen real supporting inequalities and three reality equations. Products of its generators lie in the cone, and a nonnegative three-generator decomposition extends this property to all cone points. Ten boundary edge midpoints require distinct active nonzero linear forms. A three-by-three complex diagonalizer supplies nine entry forms, and their imaginary parts vanish on the real span. The resulting contradiction refutes the cone converse and hence the conjunction in Question 9.1. The unbounded family and the separate polytope converse are outside this theorem.", DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("jp2025"), ResolutionKind.Refuted)))));
}
