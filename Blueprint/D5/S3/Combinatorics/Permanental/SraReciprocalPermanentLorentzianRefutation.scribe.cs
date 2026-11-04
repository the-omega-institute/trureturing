using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permanental;

internal sealed class SraReciprocalPermanentLorentzianRefutationDocument : IScribeDocumentDefinition
{

    private const string Prefix = "D5/S3/Combinatorics/Permanental/SraReciprocalPermanentLorentzianRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuadraticForms/sra2026koteljanskii");
    private static readonly LibraryNoteRef LorentzianSource = LibraryNoteRef.Create("D5/L/Combinatorics/brandenhuh2020lorentzian");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The reciprocal-permanent polynomial of a positive inverse M matrix need not be Lorentzian.",
        H("Sra: reciprocal-permanent Lorentzian assertion"), Blocks(
            Node("inversem", "InverseMMatrix", InverseMFormula(),
                "Source, p. 1: “A matrix A is an inverse M-matrix if A≥0 entrywise, A is invertible, and A^{-1} has nonpositive off-diagonal entries.” Invertibility is expressed by IsUnit of the determinant; indices are Fin n.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("reciprocal", "reciprocalPolynomial", ReciprocalFormula(),
                "Source, p. 6, §4(d): “For an inverse M-matrix A, consider” the displayed sum f_A(x_0,x)=∑_{S⊆[n]} per(A_S)⁻¹ x_0^{n−|S|} ∏_{i∈S} x_i. The variable none is x₀ and some i is the paper's variable xᵢ₊₁. PSW.principalPermanent uses Matrix.permanent on the subtype S; the empty permanent and product are one. Nat.sub in the exponent is truncated natural subtraction.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("positive", "positiveHomogeneous", PositiveFormula(),
                "Brändén–Huh, p. 6, §2.1: “We write H⁽ᵈ⁾ₙ for the set of degree d homogeneous polynomials in ℝ[w₁,…,wₙ].” “We define a topology on H⁽ᵈ⁾ₙ using the Euclidean norm for the coefficients, and write P⁽ᵈ⁾ₙ ⊆ H⁽ᵈ⁾ₙ for the open subset of polynomials all of whose coefficients are positive.” The formula quantifies over all degree-d exponents, including exponents outside a polynomial's support. The centered dot in the lambda denotes Lean's anonymous unused index binder _.", DescribeRole.Definition, AssessedProvenance.FromLiterature(LorentzianSource)),
            Node("hessian", "quadraticHessian", HessianFormula(),
                "Brändén–Huh, p. 6, §2.1: “The Hessian of f ∈ ℝ[w₁,…,wₙ] is the symmetric matrix” ℋ_f(w)=(∂ᵢ∂ⱼf)ᵢ,ⱼ, “where ∂ᵢ stands for the partial derivative ∂/∂wᵢ.” For a homogeneous quadratic these derivatives are constant, so their coefficients at exponent zero give that matrix.", DescribeRole.Definition, AssessedProvenance.FromLiterature(LorentzianSource)),
            Node("strict", "strictlyLorentzian", StrictFormula(),
                "Brändén–Huh, p. 7, Definition 2.1: “We set L̊⁰ₙ=P⁰ₙ, L̊¹ₙ=P¹ₙ, and L̊²ₙ={f∈P²ₙ | ℋ_f is nonsingular and has exactly one positive eigenvalue}.” “For d larger than 2, we define L̊ᵈₙ recursively by setting L̊ᵈₙ={f∈Pᵈₙ | ∂ᵢf∈L̊ᵈ⁻¹ₙ for all i∈[n]}.” The variable set here is Option(Fin n). The Hermitian eigenvalue index counts multiplicity; every eigenvalue is nonzero and exactly one index has a positive eigenvalue.", DescribeRole.Definition, AssessedProvenance.FromLiterature(LorentzianSource)),
            Node("lorentzian", "Lorentzian", LorentzianFormula(),
                "Brändén–Huh, p. 7, Definition 2.1: “The polynomials in L̊⁽ᵈ⁾ₙ are called strictly Lorentzian, and the limits of strictly Lorentzian polynomials are called Lorentzian.” The coefficient epsilon condition expresses closure in the finite-dimensional homogeneous degree-d space. The centered dot in the lambda denotes Lean's anonymous unused index binder _.", DescribeRole.Definition, AssessedProvenance.FromLiterature(LorentzianSource)),
            Node("claim", "claim", Disp(IffTo(F.Id("claim"), ClaimBody())),
                "Source, p. 6, §4(d): “Is f_A Lorentzian for every inverse M-matrix A?” The assertion quantifies over every n>0 and every real n×n inverse M matrix, with no symmetry hypothesis. Fin n index i is source index i+1.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "result", Disp(Seq(Neg, Sp, Parenthesized(ClaimBody()))),
                "The 5×5 matrix of Sra's Theorem 1.2 has positive entries and an inverse with nonpositive off-diagonal entries. Differentiating in its last three variables gives a quadratic whose Hessian is positive definite on span(e₀,e₁+e₂). This property persists for sufficiently close coefficient approximations, whereas every strictly Lorentzian quadratic has only one positive eigenvalue.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("sra2609-koteljanskii"), ResolutionKind.Refuted))), []));

    private static DocumentBlock Node(string id, string declaration, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(declaration),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Vars() =>
        Call("Option", FinN());
    private static Formula Poly() =>
        Call("MvPolynomial", Vars(), R());
    private static Formula Exponents() =>
        Call("Finsupp", Vars(), N());
    private static Formula DegreeOf(Formula a) => App(Q("Finsupp", "sum"), a, Seq(F.Id("fun"), Sp, new Formula.Placeholder(), Sp, F.Id("k"), Sp, Mapsto, Sp, F.Id("k")));
    private static Formula PositiveFormula() =>
        Disp(All("n", N(), All("d", N(), All("f", Poly(), IffTo(Call("positiveHomogeneous", F.Id("d"), F.Id("f")), And(App(Q("MvPolynomial", "IsHomogeneous"), F.Id("f"), F.Id("d")), All("a", Exponents(), ImpliesTo(EqTo(DegreeOf(F.Id("a")), F.Id("d")), LtTo(D(0), Call("coeff", F.Id("f"), F.Id("a")))))))))));
    private static Formula InverseMFormula() =>
        Disp(All("n", N(), All("A", MatN(), IffTo(Call("InverseMMatrix", F.Id("A")), And(All("i", FinN(), All("j", FinN(), LeTo(D(0), App(F.Id("A"), F.Id("i"), F.Id("j"))))), And(Call("IsUnit", App(Q("Matrix", "det"), F.Id("A"))), All("i", FinN(), All("j", FinN(), ImpliesTo(NeTo(F.Id("i"), F.Id("j")), LeTo(App(PowOf(F.Id("A"), Seq(Minus, D(1))), F.Id("i"), F.Id("j")), D(0)))))))))));
    private static Formula ReciprocalFormula() =>
        Disp(All("n", N(), All("A", MatN(),
            EqTo(Call("reciprocalPolynomial", F.Id("A")),
                SumOver("S", Finsets(),
                    TimesOf(TimesOf(
                        Call("C", PowOf(App(Q("PSW", "principalPermanent"), F.Id("A"), F.Id("S")), Seq(Minus, D(1)))),
                        PowOf(Call("X", F.Id("none")), App(Q("Nat", "sub"), F.Id("n"), App(Q("Finset", "card"), F.Id("S"))))),
                        ProductIn("i", F.Id("S"), Call("X", Call("some", F.Id("i"))))))))));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Parenthesized(Seq(Sum, Underscore, Grp(F.Id(name), Colon, type), Sp, Parenthesized(body)));
    private static Formula ProductIn(string name, Formula set, Formula body) =>
        Parenthesized(Seq(Prod, Underscore, Grp(F.Id(name), InMacro, Sp, set), Sp, Parenthesized(body)));
    private static Formula HessianFormula() =>
        Disp(All("n", N(), All("f", Poly(), EqTo(Call("quadraticHessian", F.Id("f")), LambdaOf("i", Vars(), LambdaOf("j", Vars(), Call("coeff", Call("pderiv", F.Id("i"), Call("pderiv", F.Id("j"), F.Id("f"))), D(0))))))));
    private static Formula StrictFormula() =>
        Disp(new Formula.Aligned([
            All("n", N(), All("f", Poly(), IffTo(Call("strictlyLorentzian", D(0), F.Id("f")), Call("positiveHomogeneous", D(0), F.Id("f"))))),
            All("n", N(), All("f", Poly(), IffTo(Call("strictlyLorentzian", D(1), F.Id("f")), Call("positiveHomogeneous", D(1), F.Id("f"))))),
            All("n", N(), All("f", Poly(), IffTo(Call("strictlyLorentzian", D(2), F.Id("f")), And(Call("positiveHomogeneous", D(2), F.Id("f")), Some("h", App(Q("Matrix", "IsHermitian"), Call("quadraticHessian", F.Id("f"))), And(All("i", Vars(), NeTo(App(Q("IsHermitian", "eigenvalues"), F.Id("h"), F.Id("i")), D(0))), Seq(Exists, Bang, Sp, Parenthesized(Seq(F.Id("i"), Sp, Colon, Sp, Vars())), Sp, Comma, Sp, LtTo(D(0), App(Q("IsHermitian", "eigenvalues"), F.Id("h"), F.Id("i")))))))))),
            All("n", N(), All("k", N(), All("f", Poly(), IffTo(Call("strictlyLorentzian", Add(F.Id("k"), D(3)), F.Id("f")), And(Call("positiveHomogeneous", Add(F.Id("k"), D(3)), F.Id("f")), All("i", Vars(), Call("strictlyLorentzian", Add(F.Id("k"), D(2)), Call("pderiv", F.Id("i"), F.Id("f")))))))))
        ]));
    private static Formula LorentzianFormula() =>
        Disp(All("n", N(), All("d", N(), All("f", Poly(), IffTo(Call("Lorentzian", F.Id("d"), F.Id("f")), And(App(Q("MvPolynomial", "IsHomogeneous"), F.Id("f"), F.Id("d")), All("epsilon", R(), ImpliesTo(LtTo(D(0), F.Id("epsilon")), Some("g", Poly(), And(Call("strictlyLorentzian", F.Id("d"), F.Id("g")), All("a", Exponents(), ImpliesTo(EqTo(DegreeOf(F.Id("a")), F.Id("d")), LtTo(new Formula.Absolute(Subtract(Call("coeff", F.Id("g"), F.Id("a")), Call("coeff", F.Id("f"), F.Id("a")))), F.Id("epsilon"))))))))))))));
    private static Formula ClaimBody() =>
        All("n", N(), ImpliesTo(LtTo(D(0), F.Id("n")), All("A", MatN(), ImpliesTo(Call("InverseMMatrix", F.Id("A")), Call("Lorentzian", F.Id("n"), Call("reciprocalPolynomial", F.Id("A")))))));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula App(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Some(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula ImpliesTo(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula IffTo(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula EqTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula LtTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula LeTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula NeTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula TimesOf(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula PowOf(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula LambdaOf(string name, Formula domain, Formula body) =>
        Seq(F.Id("fun"), Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, domain)), Sp, Mapsto, Sp, body);
    private static Formula R() => Seq(Mathbb, Sp, Grp(F.Id("R")));
    private static Formula N() => Seq(Mathbb, Sp, Grp(F.Id("N")));
    private static Formula FinN() => Call("Fin", F.Id("n"));
    private static Formula MatN() => Call("Matrix", FinN(), FinN(), R());
    private static Formula Finsets() => Call("Finset", FinN());
}
