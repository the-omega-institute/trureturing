using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class DeepLinearIntrinsicDimensionRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuadraticForms/DeepLinearIntrinsicDimensionRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create(
        "D5/L/QuadraticForms/arayakutynioklimalysingh2026intrinsic");
    private static Formula X(string name) => F.Id(name);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(X(owner)), Dot, Operatorname, Grp(X(name)));
    private static Formula App(Formula head, params Formula[] arguments) => new Formula.Apply(head, [.. arguments]);
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Typed(Formula a, Formula type) => Parenthesized(Seq(a, Sp, Colon, Sp, type));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Product(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Times, Sp, Parenthesized(b));
    private static Formula All(string name, Formula type, Formula body) => Seq(
        Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) => Seq(
        Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Fn(string name, Formula type, Formula body) => Seq(
        X("fun"), Sp, Typed(X(name), type), Sp, Mapsto, Sp, body);
    private static Formula SetOf(string name, Formula type, Formula body) => Seq(
        OpenBrace, Typed(X(name), type), Sp, Mid, Sp, body, CloseBrace);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(
        Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(
        Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula NN => Seq(Mathbb, Grp(X("N")));
    private static Formula RR => Seq(Mathbb, Grp(X("R")));
    private static Formula ENN => Seq(NN, Infty);
    private static Formula L => X("L");
    private static Formula T => X("theta");
    private static Formula I => X("iota");
    private static Formula Z => X("z");
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Width(Formula n) => Call("m", n);
    private static Formula Space(Formula index) => Call("EuclideanSpace", RR, index);
    private static Formula Sample(Formula index, Formula d) => Product(Arrow(Fin(d), Space(index)), Space(index));
    private static Formula Coordinates => Call("Sum", Call("Sigma", Fn("l", Fin(L),
        Product(Fin(Width(Add(Call("val", X("l")), D(1)))), Fin(Width(Call("val", X("l"))))))), Fin(Width(L)));
    private static Formula ParameterSpace => Space(Coordinates);
    private static Formula Architecture(Formula body) => All("L", NN, All("m", Arrow(NN, NN), body));
    private static Formula Indexed(Formula body) => All("iota", X("Type"), Seq(
        OpenBracket, Call("Fintype", I), CloseBracket, Comma, Sp, body));
    private static Formula Named(string name, Formula value) =>
        Parenthesized(Seq(X(name), Sp, Colon, Eq, Sp, value));
    private static Formula Solution(Formula u) => Call("solutionSet", Named("L", L), Named("m", X("m")), u);
    private static Formula Gaussian => Call("stdGaussian", Space(I));
    private static Formula First(Formula x) => Seq(x, Dot, D(1));
    private static Formula Second(Formula x) => Seq(x, Dot, D(2));
    private static Formula Hit(Formula d, Formula thetaSet) => SetOf("z", Sample(I, d),
        App(Qualified("Set", "Nonempty"), App(Qualified("Set", "inter"), Call("affinePlane", d, Z), thetaSet)));

    private static Formula ClaimBody() => Architecture(Imp(Leq(D(1), L),
        Imp(All("l", NN, Imp(Leq(X("l"), L), Leq(D(1), Width(X("l"))))),
            All("u", Arrow(Fin(Width(D(0))), RR), Imp(NotEqual(X("u"), D(0)),
                Equal(Call("intrinsicDimension", Solution(X("u"))), Typed(Width(D(0)), ENN)))))));

    private static DocumentBlock.Describe Definition(string name, Formula formula, string prose) => Describe.Lean(
        DescribeId.Create(name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name), H(name),
        StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
        Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    public DocumentDefinition Create()
    {
        var d = X("d");
        var card = App(Qualified("Fintype", "card"), I);
        var thetaSet = X("Theta");
        var sampleLaw = Indexed(All("d", NN, Equal(Call("sampleLaw", I, d),
            App(Qualified("Measure", "prod"), App(Qualified("Measure", "pi"),
                App(Qualified("Function", "const"), Fin(d), Gaussian)), Gaussian))));
        var affine = Indexed(All("d", NN, All("z", Sample(I, d), Equal(Call("affinePlane", d, Z),
            Seq(X("if"), Sp, Equal(d, card), Sp, X("then"), Sp, Qualified("Set", "univ"),
                Sp, X("else"), Sp, SetOf("x", Space(I), Member(Subtract(X("x"), Second(Z)),
                    App(Qualified("Submodule", "span"), RR, App(Qualified("Set", "range"), First(Z))))))))));
        var intrinsic = Indexed(All("Theta", Call("Set", Space(I)), Equal(Call("intrinsicDimension", thetaSet),
            Call("sInf", SetOf("n", ENN, Some("d", NN, And(Leq(d, card),
                And(Equal(X("n"), Typed(d, ENN)), Equal(App(Call("sampleLaw", I, d), Hit(d, thetaSet)), D(1))))))))));
        var weightEntry = Fn("i", Fin(Width(Add(X("l"), D(1)))), Fn("j", Fin(Width(X("l"))),
            Seq(X("if"), Sp, X("h"), Sp, Colon, Sp, Lt(X("l"), L), Sp, X("then"), Sp,
                Call("theta", App(Qualified("Sum", "inl"), Seq(Langle, Sp,
                    Seq(Langle, Sp, X("l"), Comma, Sp, X("h"), Rangle), Comma, Sp, Pair(X("i"), X("j")), Rangle))),
                Sp, X("else"), Sp, D(0))));
        var weight = Architecture(All("theta", ParameterSpace, All("l", NN,
            Equal(Call("weight", T, X("l")), weightEntry))));
        var product = Architecture(All("theta", ParameterSpace, And(
            Equal(Call("weightProduct", T, D(0)), D(1)),
            All("l", NN, Equal(Call("weightProduct", T, Add(X("l"), D(1))),
                Multiply(Call("weight", T, X("l")), Call("weightProduct", T, X("l"))))))));
        var realization = Architecture(All("theta", ParameterSpace, Equal(Call("realization", T),
            App(Qualified("Matrix", "mulVec"), App(Qualified("Matrix", "transpose"), Call("weightProduct", T, L)),
                Fn("i", Fin(Width(L)), Call("theta", App(Qualified("Sum", "inr"), X("i"))))))));
        var solution = Architecture(All("u", Arrow(Fin(Width(D(0))), RR), Equal(Solution(X("u")),
            SetOf("theta", ParameterSpace, Equal(Call("realization", T), X("u"))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Gaussian affine lines can miss the scalar deep-linear solution fiber.",
            H("The exact deep-linear intrinsic-dimension prediction fails"), Blocks(
                Definition("sampleLaw", sampleLaw,
                    "Definition 1, page 5: “Equivalently, U is obtained by taking the column space of a p × d matrix with i.i.d. N (0, 1) entries or the kernel of a (p − d) × p matrix with i.i.d. N (0, 1) entries.” Each column and the offset are independent standard Gaussian vectors. The product includes the empty family at d = 0. The finite type iota indexes ambient coordinates. Function.const displays the constant Gaussian family indexed by Fin d."),
                Definition("affinePlane", affine,
                    "Definition 1, page 5: “If d = p, we set V = Rᵖ a.s.” Otherwise the set consists of x for which x minus the independent offset lies in the real span of the sampled columns. Translating by g or its orthogonal projection gives the same affine set."),
                Definition("intrinsicDimension", intrinsic,
                    "Definition 2, page 5: “We define the intrinsic dimension” followed by equation (3). Its infimum is over integers d from zero through the ambient cardinality for which the displayed intersection event has probability one. The carrier is ENat, so an empty infimum is infinity; the displayed coercions send natural dimensions to ENat."),
                Definition("weight", weight,
                    "Section 4.1, page 21: “We say h: Rᴹ⁰ → R is a function implemented by an L-layer deep linear network with architecture m = (M₀, . . . , Mᴸ) ∈ Nᴸ⁺¹ if there are weight matrices Wℓ ∈ Rᴹℓ×ᴹℓ⁻¹ and an ouput projection a ∈ Rᴹᴸ, for ℓ ∈ [L], such that h(x) = aᵀ Wᴸ Wᴸ₋₁ · · · W₁x.” The function m records the widths. Sum.inl indexes a matrix entry by a zero-based layer and its row and column; Sum.inr indexes the output projection. Only the layers below L contribute; unused indices return zero."),
                Definition("weightProduct", product,
                    "The ordered product has identity at zero and left-multiplies by the next weight matrix at a successor. Thus weightProduct theta L is Wᴸ · · · W₁, with no reversal of the matrix order."),
                Definition("realization", realization,
                    "Equation (20), page 22, uses W₁ᵀ W₂ᵀ · · · Wᴸᵀ a. This is the transpose of the ordered product applied to the output coordinates. All matrices and vectors are real."),
                Definition("solutionSet", solution,
                    "Equation (20), page 22: Θ = {(W₁, . . . , Wᴸ, a) : W₁ᵀ W₂ᵀ · · · Wᴸᵀ a = u⋆}. These are the bias-free coordinates of that tuple and of Theorem 17. The paragraph following equation (20) contains bias coordinates inconsistent with this displayed tuple; they are not coordinates of the displayed polynomial fiber."),
                Definition("claim", new Formula.Logic(X("claim"), FormulaLogicOperator.Iff, Parenthesized(ClaimBody())),
                    "Page 23: “As we will see in Section 7, numerical experiments suggest that dᵢₙₜ(Θ) = D in the deep linear case independently of the width and depth of the network.” Here L is positive, every m l for l at most L is positive, D is m 0, and the target u is nonzero. The ambient coordinate type has one coordinate for each weight entry and each output entry. The assertion quantifies all these architectures and targets."),
                Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                    H("Negation of the complete exact-value prediction"),
                    StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(ClaimBody())))),
                    AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(
                        "Take L = 1, every width equal to one, and target u = 1. The fiber is the hyperbola wa = 1. A sampled point with wa < 1 misses it. For a sampled line g + tv, its intersection equation has coefficients A = v₁v₂, B = g₁v₂ + v₁g₂, and C = g₁g₂ − 1. The open region A < 0 with negative discriminant contains v = (1, −1), g = 0, so Gaussian full support gives it positive measure. The quadratic equation has no real root there. Hence neither dimension zero nor dimension one has intersection probability one. The infimum is at least two, contradicting the asserted value one. This argument proves a global affine-intersection obstruction; it does not evaluate general widths or depths."))), DescribeRole.Theorem,
                    openProblemResolutionClaim: new OpenProblemResolutionClaim(
                        ProblemSlugRef.Create("araya-kutyniok-li-maly-singh-intrinsic-dimension"),
                        ResolutionKind.Refuted)))));
    }
}
