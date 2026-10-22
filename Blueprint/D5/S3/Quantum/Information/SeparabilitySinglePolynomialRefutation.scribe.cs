using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class SeparabilitySinglePolynomialRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/SeparabilitySinglePolynomialRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumContext/krugerwerner2005openproblems");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An affine family of qubit–qutrit density operators excludes a single polynomial inequality characterizing separability, even when the polynomial may depend on the local dimensions.",
        H("No single polynomial inequality characterizes bipartite separability"),
        Blocks(
            Node("coords", "Real and imaginary matrix coordinates", CoordinatesFormula(),
                AssessedProvenance.FromRepo(Source), DescribeRole.Definition,
                Paragraph(Text("For a bipartite complex matrix, the coordinate indexed by (p,q,b) is the imaginary part of the entry at (p,q) when b is true, and its real part otherwise. The index type is (Fin m × Fin n) × ((Fin m × Fin n) × Bool). This concrete coordinate encoding expresses real polynomials in matrix entries; it imposes no positivity or normalization condition."))),
            Node("IsInvariant", "Polynomial invariance on density operators", InvariantFormula(),
                AssessedProvenance.FromLiterature(Source), DescribeRole.Definition,
                Paragraph(Text("Krüger–Werner, Problem 3, defines equally entangled states by conjugation with arbitrary local unitaries, and an entanglement invariant as a real function constant on these orbits. A polynomial invariant is polynomial in the matrix entries. Real and imaginary coordinates express such a function as a real multivariate polynomial. Density operators are positive semidefinite matrices with trace one:")),
                new DocumentBlock.DisplayFormula(Disp(DensityFormula())),
                Paragraph(Text("The displayed invariance condition is required only on density operators. Each local unitary is explicitly coerced to its complex matrix before taking the tensor product, and the final factor is the conjugate transpose of that tensor product."))),
            Node("claim", "The single-inequality separability question", ClaimFormula(),
                AssessedProvenance.FromLiterature(Source), DescribeRole.Definition,
                Paragraph(Text("The third closely related problem in Problem 3 asks for a polynomial invariant f such that f(ρ) ≥ 0 is equivalent to separability, allowing f to depend on the dimensions. Here m and n range over all natural local dimensions at least two. For each pair of dimensions one polynomial must classify every density operator. The predicate separableCone means a finite sum of tensor products of positive semidefinite matrices; at trace one this is precisely a separable state. No degree bound is imposed. The source's solution using separation of compact-group orbits answers the main completeness question for polynomial invariants; it does not answer this single-inequality subquestion."))),
            Node("result", "An affine qubit–qutrit family gives a contradiction", Disp(new Formula.Not(Named("claim"))),
                AssessedProvenance.FromRepo(Source), DescribeRole.Theorem,
                Paragraph(Text("Take local dimensions m = 2 and n = 3. In the ordered basis e₀ = |00⟩, e₁ = |01⟩, e₂ = |02⟩, e₃ = |10⟩, e₄ = |11⟩, e₅ = |12⟩, define the real symmetric matrix ρ(x,y) by the diagonal (a,b,c,c,a,b), where a = (5 + 3x − y)/40, b = (5 − x + 3y)/40 and c = (5 − x − y)/20. Its only nonzero off-diagonal entries are ρ₁₃ = ρ₃₁ = (−5 + 5x + y)/40 and ρ₂₄ = ρ₄₂ = (−5 + x + 5y)/40. All these real entries are embedded in ℂ. The trace is one, and the family is affine: writing B₀ = ρ(0,0), B₁ = ρ(1,0) and B₂ = ρ(0,1), one has ρ(x,y) = (1 − x − y)B₀ + xB₁ + yB₂.")),
                Paragraph(Text("For a complex vector v write P(v) = vvᴴ, without normalizing v. The identity ρ(x,y) = Σⱼ cⱼ P(vⱼ) has the eight vectors (e₀, e₅, 2e₁ − 3e₃, 2e₄ − 3e₂, e₁, e₄, e₃, e₂) and the corresponding real coefficients ((5 + 3x − y)/40, (5 − x + 3y)/40, (5 − 5x − y)/240, (5 − x − 5y)/240, (5 + 7x + 11y)/120, (5 + 11x + 7y)/120, (5 + 11x − y)/80, (5 − x + 11y)/80). Each coefficient is nonnegative when |x|,|y| ≤ 1/4. Thus every matrix in this square is a density operator.")),
                Paragraph(Text("The three corner states have explicit product decompositions. Each is a sum Σⱼ cⱼ P(aⱼ) ⊗ P(bⱼ). For B₀, the pairs (aⱼ,bⱼ) are ((1,1),(1,−1,1)), ((1,i),(−1,i,1)), ((1,−1),(1,1,1)), ((1,−i),(−1,−i,1)), ((1,0),(0,0,1)) and ((0,1),(1,0,0)); the coefficients are (1/32,1/32,1/32,1/32,1/8,1/8). For both B₁ and B₂ the first-factor vectors are ((1,1),(1,i),(1,−1),(1,−i),(1,0),(0,1),(1,0),(0,1)), and the coefficients are (1/40,1/40,1/40,1/40,1/10,1/10,1/5,1/5). For B₁ the second-factor vectors are ((0,1,−1),(0,1,−i),(0,1,1),(0,1,i),(0,0,1),(0,1,0),(1,0,0),(1,0,0)); for B₂ they are ((1,−1,0),(1,−i,0),(1,1,0),(1,i,0),(0,1,0),(1,0,0),(0,0,1),(0,0,1)). Here i is the imaginary unit, and all vectors are unnormalized. These sums are separable and have trace one. If 0 ≤ x,y ≤ 1/4, the affine coefficients 1 − x − y, x and y are nonnegative, so ρ(x,y) is separable.")),
                Paragraph(Text("Let Γ transpose the qutrit factor. The real quadratic forms of Γ(ρ(x,y)) on e₀ + e₄ and e₁ + e₅ are 2x/5 and 2y/5, respectively. Every separable matrix has positive semidefinite partial transpose. Hence ρ(x,y) is entangled whenever x < 0 or y < 0 and |x|,|y| ≤ 1/4.")),
                Paragraph(Text("Suppose a polynomial f satisfies the claimed equivalence at dimensions 2 and 3, and put q(x,y) = f(ρ(x,y)), meaning evaluation in the real and imaginary entry coordinates. Affineness makes q a polynomial. Fix 0 < y < 1/4. Separability at x = 0 gives q(0,y) ≥ 0, whereas entanglement for −1/4 < x < 0 gives q(x,y) < 0. Continuity as x tends to zero from below forces q(0,y) = 0. The univariate polynomial y ↦ q(0,y) therefore has infinitely many roots and is identically zero. In particular q(0,−1/8) = 0 ≥ 0, although ρ(0,−1/8) is a density operator with a negative partial-transpose quadratic form. This contradicts the proposed equivalence. The argument uses neither local-unitary invariance nor a degree bound. The affine family and all the decompositions above are constructions here."))))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        AssessedProvenance provenance, DescribeRole role, params DocumentBlock[] explanation) => Describe.Lean(
            DescribeId.Create("kw-single-polynomial-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(explanation), role);

    private static Formula Named(string name) => Seq(Operatorname, Grp(name.Split('.')
        .SelectMany((part, index) => index == 0 ? new[] { F.Id(part) } : new Formula[] { Dot, F.Id(part) })
        .ToArray()));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(variable, Colon, Sp, type)), Comma, Sp, Parenthesized(body));
    private static Formula Some(Formula variable, Formula type, Formula body) =>
        Seq(Exists, Sp, Parenthesized(Seq(variable, Colon, Sp, type)), Comma, Sp, Parenthesized(body));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula EqTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LeTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula IffTo(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Product(Formula left, Formula right) =>
        Parenthesized(Seq(left, Sp, Times, Sp, right));
    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Joint => Product(Call("Fin", F.Id("m")), Call("Fin", F.Id("n")));
    private static Formula Mat => Call("Matrix", Joint, Joint, Complexes);
    private static Formula CoordinateIndex => Product(Joint, Product(Joint, Named("Bool")));
    private static Formula Polynomial => Call("MvPolynomial", CoordinateIndex, Reals);
    private static Formula Dimensions(Formula body) => All(F.Id("m"), Naturals, All(F.Id("n"), Naturals, body));
    private static Formula MatrixCast(Formula unitary, Formula dimension) => Parenthesized(
        Seq(Call("Subtype.val", unitary), Colon, Sp,
            Call("Matrix", Call("Fin", dimension), Call("Fin", dimension), Complexes)));
    private static Formula Eval(Formula matrix, Formula polynomial) =>
        Call("MvPolynomial.eval", Call("coords", matrix), polynomial);

    private static Formula DensityFormula() => Dimensions(All(Rho, Mat,
        IffTo(Call("IsDensity", Rho), And(Call("Matrix.PosSemidef", Rho),
            EqTo(Call("Matrix.trace", Rho), D(1))))));

    private static Formula CoordinatesFormula()
    {
        Formula p = F.Id("p"), q = F.Id("q"), b = F.Id("b");
        Formula entry = new Formula.Apply(Rho, [p, q]);
        Formula triple = Parenthesized(Seq(p, Comma, Sp, Parenthesized(Seq(q, Comma, Sp, b))));
        return Disp(Dimensions(All(Rho, Mat, All(p, Joint, All(q, Joint, All(b, Named("Bool"),
            EqTo(new Formula.Apply(Call("coords", Rho), [triple]),
                Call("ite", EqTo(b, Named("true")), Call("Complex.im", entry), Call("Complex.re", entry)))))))));
    }

    private static Formula InvariantFormula()
    {
        Formula f = F.Id("f"), ua = F.Id("UA"), ub = F.Id("UB");
        Formula local = Call("Matrix.kronecker", MatrixCast(ua, F.Id("m")), MatrixCast(ub, F.Id("n")));
        Formula conjugated = Mul(Mul(local, Rho), Call("Matrix.conjTranspose", local));
        return Disp(Dimensions(All(f, Polynomial, IffTo(Call("IsInvariant", f),
            All(ua, Call("Matrix.unitaryGroup", Call("Fin", F.Id("m")), Complexes),
                All(ub, Call("Matrix.unitaryGroup", Call("Fin", F.Id("n")), Complexes),
                    All(Rho, Mat, Arrow(Call("IsDensity", Rho), EqTo(Eval(conjugated, f), Eval(Rho, f))))))))));
    }

    private static Formula ClaimFormula()
    {
        Formula f = F.Id("f");
        Formula criterion = IffTo(LeTo(D(0), Eval(Rho, f)), Call("separableCone", Rho));
        Formula states = All(Rho, Mat, Arrow(Call("IsDensity", Rho), criterion));
        Formula polynomial = Some(f, Polynomial, And(Call("IsInvariant", f), states));
        Formula body = Dimensions(Arrow(LeTo(D(2), F.Id("m")), Arrow(LeTo(D(2), F.Id("n")), polynomial)));
        return Disp(IffTo(Named("claim"), body));
    }
}
