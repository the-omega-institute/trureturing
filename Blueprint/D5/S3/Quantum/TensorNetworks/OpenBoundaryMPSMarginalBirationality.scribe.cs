using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class OpenBoundaryMPSMarginalBirationalityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSMarginalBirationality";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Geometry/critchmorton2014mps");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every three-site improper marginal of an open-boundary binary bond-two matrix product state has a rational inverse on a nonempty Zariski-open subset.",
        H("Rational reconstruction from three consecutive sites"),
        Blocks(
            Definition("mps-state", "mpsState", "Open-boundary amplitudes", StateFormula(),
                "The amplitude of the word w is b₀ᵀA[w(0)]⋯A[w(n−1)]b₁, with A₀ = a₀ and A₁ = a₁. "
                    + "The matrices are the same at every site, and the two boundary vectors are independent. "
                    + "The dot product is bilinear over the complex numbers, without conjugation. "
                    + "The list product preserves the site order and is the identity matrix when n is zero. "
                    + "This is equation (eqn-phi2) of the source, sigma14-095.tex, lines 349–358, specialized to physical and bond dimensions two.",
                AssessedProvenance.FromLiterature(Source)),
            Definition("open-boundary-mps", "openBoundaryMPS", "The parametrized model", ModelFormula(),
                "The model consists of all amplitude functions obtained by varying the two complex two-by-two matrices and both complex boundary vectors. "
                    + "It is OB(2,2,n) in the source, sigma14-095.tex, lines 360–363.",
                AssessedProvenance.FromLiterature(Source)),
            Definition("vanishing-polys", "vanishingPolys", "The vanishing ideal", IdealFormula(),
                "These are all complex polynomials in the word coordinates that vanish on every state in the parametrized model. "
                    + "They are the equations used to take the Zariski closure of OB(2,2,n), as in sigma14-095.tex, lines 360–363.",
                AssessedProvenance.FromLiterature(Source)),
            Definition("closure", "closure", "The affine Zariski closure", ClosureFormula(),
                "The closure is the common zero set of the vanishing ideal of the parametrized model. "
                    + "Thus it is the affine Zariski closure, denoted by the closure of OB(2,2,n) in the source, sigma14-095.tex, lines 360–363.",
                AssessedProvenance.FromLiterature(Source)),
            Definition("improper-marginal", "improperMarginal", "Summing outside a consecutive triple", MarginalFormula(),
                "For each three-letter word t, sum the amplitudes of all n-letter words whose letters at positions a, a+1 and a+2 equal t. "
                    + "This sums every index outside the three consecutive sites, as in sigma14-095.tex, lines 420–426. "
                    + "The sum is coherent in complex amplitudes. The bound a+3 ≤ n makes each selected index valid; "
                    + "Fin.val is the inclusion of a finite index into the natural numbers. The proof h of the indexing bound is an explicit argument.",
                AssessedProvenance.FromLiterature(Source)),
            Definition("is-birational-via", "IsBirationalVia", "A rational inverse on principal open subsets", BirationalFormula(),
                "The polynomials g and q and the coordinate polynomials p give the rational map F(t)(w) = p(w)(t)/q(t). "
                    + "The three conjuncts say respectively that the source chart is nonempty, that F maps the target chart into the source chart and is a right inverse there, "
                    + "and that F is a left inverse on the source chart, with the denominator nonzero on both charts. "
                    + "Write Xₙ for the affine closure. Since the linear marginal takes the parametrized models into one another, it also takes their Zariski closures into one another. "
                    + "Consequently these conditions express the isomorphism between the nonempty Zariski-open subsets "
                    + "U = {ψ ∈ Xₙ : g(mψ) ≠ 0} and V = {t ∈ X₃ : g(t) ≠ 0}, given by the marginal and its rational inverse. "
                    + "For irreducible Xₙ and X₃ these subsets are dense. The proof h of the indexing bound is an explicit argument.",
                AssessedProvenance.FromRepo(Source)),
            Definition("claim", "claim", "The three-site birationality conjecture", Equal(Local("claim"), Parenthesized(ClaimFormula())),
                "For every natural n at least four and every starting position a with a+3 ≤ n, "
                    + "the two vanishing ideals are prime and the improper marginal has the rational inverse described by the three clauses. "
                    + "This states Conjecture 8, sigma14-095.tex, lines 430–434, with birational equivalence expressed by rational maps on nonempty principal open subsets.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("Birationality of every consecutive three-site marginal"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "First express each word amplitude as a polynomial in the twelve matrix and boundary entries. "
                            + "Substitution into these polynomials is a homomorphism from the coordinate polynomial ring to the parameter polynomial ring. "
                            + "Its kernel equals the vanishing ideal: evaluation on all complex parameter values detects a zero polynomial. "
                            + "The parameter polynomial ring is an integral domain, so this kernel is prime. "
                            + "This applies to every length, in particular n and three.")),
                    Paragraph(Text(
                        "For a three-site tensor t, let Tⱼ have entries t(i,j,k), and form the four-by-four matrix K(t) whose row (i,k) is "
                            + "(t(i,k,0), t(i,k,1), −t(0,i,k), −t(1,i,k)). Its determinant is a quartic vanishing on the three-site model. "
                            + "To see this as a polynomial identity, let U have rows b₀ᵀAᵢ and W have columns Aₖb₁. "
                            + "The vectors z = det(U) adj(W)b₁ and e = det(W)b₀ᵀadj(U) satisfy K(t)(z₀,z₁,e₀,e₁)ᵀ = 0. "
                            + "The component e₀ is a nonzero parameter polynomial, as is seen with A₀ the identity, A₁ the exchange matrix and both boundaries (1,0). "
                            + "The determinant therefore vanishes identically in the parameter domain. "
                            + "It belongs to the vanishing ideal, so det K(t) = 0 on X₃ as well. "
                            + "The source's three-site quartic hypersurface is described in sigma14-095.tex, lines 378–406.")),
                    Paragraph(Text(
                        "Let d be the determinant of the leading three-by-three minor of K, and let Δ₀, Δ₁, Δ₂ be its Cramer determinants for minus the first three entries of the last column of K. "
                            + "The polynomial identity K(Δ₀,Δ₁,Δ₂,d)ᵀ = (0,0,0,det K)ᵀ gives, when d ≠ 0, "
                            + "a kernel vector (z₀,z₁,ℓ₀,1) with z = (Δ₀,Δ₁)/d and ℓ = (Δ₂,d)/d. "
                            + "The nonzero minor also makes every kernel vector proportional to this one. "
                            + "Put Vᵢₖ = (ℓTᵢ)ₖ, Bⱼ = TⱼV⁻¹, r = Vz and C = B₀+B₁. "
                            + "For the polynomial chart, put L = (Δ₂,d), Z = (Δ₀,Δ₁), Wᵢₖ = (LTᵢ)ₖ, Hⱼ = Tⱼadj(W), H = H₀+H₁ and R = WZ; thus W = dV on d ≠ 0. "
                            + "Take g to be d det(W) det(H) times the two minors "
                            + "t(0,0,0)t(1,0,1)−t(0,0,1)t(1,0,0) and t(0,0,0)t(0,1,1)−t(0,0,1)t(0,1,0). "
                            + "On g ≠ 0 both V and C are invertible. The kernel equations give Tₖz = Veₖ, while the definition of V gives ℓBᵢ = eᵢᵀ. "
                            + "It follows that Bₖr = Veₖ and ℓBᵢBⱼBₖr = t(i,j,k). Thus the reconstructed parameters reproduce t.")),
                    Paragraph(Text(
                        "For b = n−3−a, define Fₙ,ₐ(t)(w) = ℓ(C⁻¹)ᵃB[w(0)]⋯B[w(n−1)](C⁻¹)ᵇr. "
                            + "This is a rational map with common denominator q = det(W)³ det(H)ⁿ⁻³ and coordinate numerator "
                            + "p(w) = L adj(H)ᵃH[w(0)]⋯H[w(n−1)]adj(H)ᵇR. "
                            + "Indeed Bⱼ = (d/det W)Hⱼ, ℓ = L/d, r = R/d² and C⁻¹ = (det W/(d det H))adj(H); substituting these expressions and using n = a+b+3 gives exactly p(w)/q. "
                            + "The chart makes q nonzero. The expression for F is an n-site state with matrices B₀,B₁ and boundaries ℓ(C⁻¹)ᵃ and (C⁻¹)ᵇr, so it lies in the model and hence in Xₙ. "
                            + "Splitting a word into its prefix, middle triple and suffix shows that summing all length-k outside words replaces their matrix products by Cᵏ. "
                            + "The outside sums therefore cancel the inverse powers on both sides, leaving the reconstructed triple t. "
                            + "Hence mF(t) = t, and g(mF(t)) = g(t) ≠ 0.")),
                    Paragraph(Text(
                        "For uniqueness first take an actual n-site state with matrices A₀,A₁ and boundaries α,β. "
                            + "Write S = A₀+A₁, l = αᵀSᵃ and r′ = Sᵇβ for its marginal boundaries. "
                            + "Let U have rows lAᵢ and W have columns Aₖr′. The nonzero endpoint minor of the triple makes both U and W invertible, since T₀ = UA₀W. "
                            + "The vector (W⁻¹r′, lU⁻¹) is in the kernel of K. Its last component s is nonzero: otherwise kernel uniqueness makes the whole vector zero, contradicting invertibility of W. "
                            + "Comparison with the normalized Cramer vector gives ℓ = s⁻¹lU⁻¹, Bⱼ = sUAⱼU⁻¹ and r = s⁻²Ur′. "
                            + "In particular C = sUSU⁻¹. Conjugation cancels throughout the word product, and the total scalar in F is sⁿs⁻¹s⁻ᵃs⁻ᵇs⁻² = 1 because n = a+b+3. "
                            + "Thus F(mψ) = ψ on the parametrized model wherever g(mψ) ≠ 0.")),
                    Paragraph(Text(
                        "Extend this equality to Xₙ coordinate by coordinate. Pull back g, q and p(w) along the linear marginal. "
                            + "The polynomial (g∘m)((p(w)∘m)−ψ(w)(q∘m)) vanishes on the model: "
                            + "when g(mψ) is zero the first factor vanishes, and otherwise uniqueness and the nonzero denominator make the second factor vanish. "
                            + "It therefore vanishes on Xₙ. On the chart, cancel g(mψ) and divide by q(mψ), obtaining F(mψ) = ψ on the closure.")),
                    Paragraph(Text(
                        "Finally there exists a triple t in X₃ with g(t) ≠ 0. To prove this, choose A₀ = ((1,2),(3,4)), A₁ = ((5,6),(7,8)), b₀ = (1,0) and b₁ = (1,2). "
                            + "The resulting triple, in lexicographic word order, is (145,349,337,829,489,1173,1193,2933). "
                            + "At this point d = 387072 and (Δ₀,Δ₁,Δ₂) = (118272,10752,−1161216); the reconstructed determinants are det V = 1152 and det C = −2, "
                            + "and the two endpoint minors are −576 and 2592. Every factor of g is nonzero. "
                            + "Thus the target chart contains a point t, and Fₙ,ₐ sends any such point to a point of Xₙ whose marginal is t. "
                            + "The existence of t supplies the nonempty source chart for every n, a and bound proof h in the stated range. Together with primeness and the two inverse identities, this proves all three clauses."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("critch-morton-2014-open-boundary-mps-marginal-birationality"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Definition(string id, string declaration, string title, Formula formula,
        string prose, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration), H(title),
        StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))),
        DescribeRole.Definition);

    private static Formula StateFormula()
    {
        Formula matrices = Typed(Vector2(X("a₀"), X("a₁")), Arrow(FinOf(D(2)), Matrices()));
        Formula product = At(Qualified("List", "prod"), At(Qualified("List", "ofFn"),
            LambdaOf("j", FinOf(X("n")), At(matrices, At(X("w"), X("j"))))));
        Formula body = LambdaOf("w", Words(X("n")), At(Qualified("dotProduct"), X("b₀"),
            At(Qualified("Matrix", "mulVec"), product, X("b₁"))));
        return All("n", Naturals(), All("a₀", Matrices(), All("a₁", Matrices(),
            All("b₀", Boundary(), All("b₁", Boundary(),
                Equal(LocalCall("mpsState", X("n"), X("a₀"), X("a₁"), X("b₀"), X("b₁")), body))))));
    }

    private static Formula ModelFormula() => All("n", Naturals(),
        Equal(LocalCall("openBoundaryMPS", X("n")), Seq(OpenBrace, Typed(X("ψ"), States(X("n"))), Sp, Mid, Sp,
            Parenthesized(Some("a₀", Matrices(), Some("a₁", Matrices(), Some("b₀", Boundary(), Some("b₁", Boundary(),
                Equal(X("ψ"), LocalCall("mpsState", X("n"), X("a₀"), X("a₁"), X("b₀"), X("b₁")))))))), CloseBrace)));

    private static Formula IdealFormula() => All("n", Naturals(),
        Equal(LocalCall("vanishingPolys", X("n")), At(Qualified("MvPolynomial", "vanishingIdeal"),
            Complexes(), LocalCall("openBoundaryMPS", X("n")))));

    private static Formula ClosureFormula() => All("n", Naturals(),
        Equal(Closed(X("n")), At(Qualified("MvPolynomial", "zeroLocus"),
            Complexes(), LocalCall("vanishingPolys", X("n")))));

    private static Formula MarginalFormula()
    {
        Formula index = Typed(At(Qualified("Fin", "mk"),
            Add(X("a"), Typed(At(Qualified("Fin", "val"), X("j")), Naturals()))), FinOf(X("n")));
        Formula middle = LambdaOf("j", FinOf(D(3)), At(X("w"), index));
        Formula summand = At(Qualified("ite"), Equal(middle, X("t")),
            At(X("ψ"), X("w")), Typed(D(0), Complexes()));
        Formula sum = Seq(new Formula.Subscript(Sum, Typed(X("w"), Words(X("n")))),
            Sp, Parenthesized(summand));
        return All("n", Naturals(), All("a", Naturals(), All("h", IndexBound(), All("ψ", States(X("n")),
            Equal(Marginal(X("ψ"), X("h")), LambdaOf("t", Words(D(3)), sum))))));
    }

    private static Formula BirationalFormula() => All("n", Naturals(), All("a", Naturals(),
        All("h", IndexBound(), Equal(LocalCall("IsBirationalVia", X("n"), X("a"), X("h")), Parenthesized(BirationalBody())))));

    private static Formula BirationalBody()
    {
        Formula sourcePoint = Some("ψ", States(X("n")), And(Member(X("ψ"), Closed(X("n"))),
            Nonzero(Evaluate(Marginal(X("ψ"), X("h")), X("g")))));
        Formula targetInverse = All("t", States(D(3)), Imp(Member(X("t"), Closed(D(3))),
            Imp(Nonzero(Evaluate(X("t"), X("g"))),
                And(Nonzero(Evaluate(X("t"), X("q"))),
                    And(Member(Rational(X("t")), Closed(X("n"))),
                        And(Nonzero(Evaluate(Marginal(Rational(X("t")), X("h")), X("g"))),
                            Equal(Marginal(Rational(X("t")), X("h")), X("t"))))))));
        Formula sourceInverse = All("ψ", States(X("n")), Imp(Member(X("ψ"), Closed(X("n"))),
            Imp(Nonzero(Evaluate(Marginal(X("ψ"), X("h")), X("g"))),
                And(Nonzero(Evaluate(Marginal(X("ψ"), X("h")), X("q"))),
                    Equal(Rational(Marginal(X("ψ"), X("h"))), X("ψ"))))));
        return Some("g", Polynomials(), Some("q", Polynomials(),
            Some("p", Arrow(Words(X("n")), Polynomials()), And(sourcePoint, And(targetInverse, sourceInverse)))));
    }

    private static Formula ClaimFormula() => All("n", Naturals(), All("a", Naturals(),
        Imp(LE(D(4), X("n")), All("h", IndexBound(),
            And(At(Qualified("Ideal", "IsPrime"), LocalCall("vanishingPolys", X("n"))),
                And(At(Qualified("Ideal", "IsPrime"), LocalCall("vanishingPolys", D(3))),
                    LocalCall("IsBirationalVia", X("n"), X("a"), X("h"))))))));

    private static Formula Rational(Formula t) => LambdaOf("w", Words(X("n")),
        new Formula.Fraction(Evaluate(t, At(X("p"), X("w"))), Evaluate(t, X("q"))));
    private static Formula Evaluate(Formula t, Formula polynomial) => At(Qualified("MvPolynomial", "eval"), t, polynomial);
    private static Formula Marginal(Formula state, Formula h) => LocalCall("improperMarginal", X("n"), X("a"), h, state);
    private static Formula Closed(Formula n) => LocalCall("closure", n);
    private static Formula IndexBound() => LE(Add(X("a"), D(3)), X("n"));
    private static Formula Polynomials() => At(Qualified("MvPolynomial"), Words(D(3)), Complexes());
    private static Formula States(Formula n) => Arrow(Words(n), Complexes());
    private static Formula Words(Formula n) => Arrow(FinOf(n), FinOf(D(2)));
    private static Formula Boundary() => Arrow(FinOf(D(2)), Complexes());
    private static Formula Matrices() => At(Qualified("Matrix"), FinOf(D(2)), FinOf(D(2)), Complexes());
    private static Formula FinOf(Formula n) => At(Qualified("Fin"), n);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Vector2(Formula a, Formula b) => Seq(Bang, OpenBracket, a, Comma, Sp, b, CloseBracket);
    private static Formula X(string name) => name switch
    {
        "ψ" => Psi,
        "a₀" => new Formula.Subscript(F.Id("a"), D(0)),
        "a₁" => new Formula.Subscript(F.Id("a"), D(1)),
        "b₀" => new Formula.Subscript(F.Id("b"), D(0)),
        "b₁" => new Formula.Subscript(F.Id("b"), D(1)),
        _ => F.Id(name),
    };
    private static Formula Local(string name) => Qualified(name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => new Formula.LatexSequence([Open, value, Close]);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body)));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula Imp(Formula premise, Formula conclusion) =>
        new Formula.Logic(Parenthesized(premise), FormulaLogicOperator.Implies, Parenthesized(conclusion));
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Member(Formula value, Formula set) => new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);
    private static Formula Nonzero(Formula value) => new Formula.Relation(value, FormulaRelationOperator.NotEqual, Typed(D(0), Complexes()));
}
