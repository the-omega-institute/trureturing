using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra;

internal sealed class TensorNullSummandDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/HomologicalAlgebra/TensorNullSummand.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Semigroups/he2025tensor");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A tensor power of every singular finite-semigroup representation contains a one-dimensional null summand; every indecomposable-summand count is asymptotic to the tensor dimension.",
        H("He–Tubbenhauer: a null summand in a tensor power"),
        Blocks(
            Node("HasNullSummand", "A one-dimensional null direct summand", NullDefinition(),
                "Section 4, page 17: “Unlike in the monoid case, the null representation Z with all elements in S acting as 0 is admitted as a kS-module, and it forms a tensor ideal (in the sense that V⊗Z=Z^{⊕dim V} for all V.)” The summand L has dimension one, every action vanishes on L, and its complementary subspace U is invariant under every action. The complement is an invariant direct summand, rather than a composition factor.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("IsIndecomposableSummand", "An indecomposable invariant subspace", IndecomposableDefinition(),
                "Section 1, page 1 defines b(n) as “# M-indecomposable summands of V^{⊗n} (counted with multiplicity)”. Section 4 applies the growth question to nonunital semigroup modules. A nonzero invariant subspace P is indecomposable when every decomposition into disjoint invariant subspaces Q and R has a zero factor. All three subspaces lie in the same ambient W.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("IsSummandCount", "The number of indecomposable summands", CountDefinition(),
                "Section 1, page 1: “b(n)=b^{M,V}(n)=# M-indecomposable summands of V^{⊗n} (counted with multiplicity).” A family indexed by Fin b records b individual summands, so repeated isomorphic factors are counted separately. DirectSum.IsInternal states that the natural sum of the subspace inclusions is bijective.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("tensorAction", "The diagonal action on a tensor power", TensorDefinition(),
                "Section 4, page 17, Conjecture 4.2 refers to “V^{⊗m}”. TensorPower k n W is Mathlib's tensor product indexed by Fin n, and PiTensorProduct.map applies the same endomorphism rho(s) to each factor. The centered dot in the displayed function is an anonymous index. The map rho is multiplicative and need not preserve an identity.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Conjecture 4.2", IffTo(V("claim"), ClaimBody()),
                "Conjecture 4.2, page 17: “Let V be a kS-module on which no element acts invertibly, then there is some m ≥ 1 such that Z is a summand of V^{⊗m}, and consequently a(n)=(dim V)ⁿ.” The field is algebraically closed, S is a nonempty finite semigroup without a two-sided identity, V is finite dimensional, and rho is a nonunital representation. Section 1, page 1 defines asymptotic equality by a ratio tending to one. The second conjunct supplies a count sequence; the third proves the ratio limit for every such sequence. In particular, the limit does not depend on selecting one decomposition.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The null-summand conjecture holds", ClaimBody(),
                "Write K for the intersection of the operator kernels and I for the sum of their images. A complement of K∩I in K is disjoint from I and extends to an invariant direct-sum decomposition. Its dimension is at least the ambient dimension minus twice the sum of the operator ranks. Tensor ranks are at most the corresponding powers of the original ranks. Every original rank is smaller than dim V, so geometric decay gives a positive exponent with a null line. Strong induction on dimension supplies finite indecomposable decompositions. In every such decomposition, the number of factors lies between the tensor dimension minus twice the sum of the tensor ranks and the tensor dimension. The squeeze theorem gives the stated universal limit. These dimension and convergence arguments work over any field and do not require absence of a semigroup identity.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("ht2508"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role, openProblemResolutionClaim: resolution);

    private static Formula DefinitionBase(Formula body) =>
        All("k", V("Type"), All("S", V("Type"), All("W", V("Type"),
        Inst(Call("Field", V("k")), Inst(Call("AddCommGroup", V("W")),
        Inst(Call("Module", V("k"), V("W")),
        All("a", Arrow(V("S"), Endomorphism(V("W"))), body)))))));

    private static Formula NullDefinition() => DefinitionBase(
        IffTo(Call("HasNullSummand", V("a")),
            Some("L", Subspace(V("W")), Some("U", Subspace(V("W")),
            And(EqTo(Rank(V("L")), D(1)),
            And(Call("IsCompl", V("L"), V("U")),
            And(All("s", V("S"), All("x", V("W"),
                    ImpliesTo(Member(V("x"), V("L")), EqTo(App(V("a"), V("s"), V("x")), D(0))))),
                Invariant(V("U")))))))));

    private static Formula IndecomposableDefinition() => DefinitionBase(
        All("P", Subspace(V("W")),
        IffTo(Call("IsIndecomposableSummand", V("a"), V("P")),
        And(NeTo(V("P"), Qualified("Bot", "bot")), And(Invariant(V("P")),
        All("Q", Subspace(V("W")), All("R", Subspace(V("W")),
        ImpliesTo(LeTo(V("Q"), V("P")), ImpliesTo(LeTo(V("R"), V("P")),
        ImpliesTo(Invariant(V("Q")), ImpliesTo(Invariant(V("R")),
        ImpliesTo(Call("Disjoint", V("Q"), V("R")),
        ImpliesTo(EqTo(App(Qualified("Max", "max"), V("Q"), V("R")), V("P")),
            Or(EqTo(V("Q"), Qualified("Bot", "bot")), EqTo(V("R"), Qualified("Bot", "bot"))))))))))))))));

    private static Formula CountDefinition() => DefinitionBase(
        All("b", N(), IffTo(Call("IsSummandCount", V("a"), V("b")),
        Some("P", Arrow(Call("Fin", V("b")), Subspace(V("W"))),
        And(App(Qualified("DirectSum", "IsInternal"), V("P")),
            All("i", Call("Fin", V("b")),
                Call("IsIndecomposableSummand", V("a"), App(V("P"), V("i")))))))));

    private static Formula TensorDefinition() =>
        All("k", V("Type"), All("S", V("Type"), All("W", V("Type"),
        Inst(Call("Field", V("k")), Inst(Call("Semigroup", V("S")),
        Inst(Call("AddCommGroup", V("W")), Inst(Call("Module", V("k"), V("W")),
        All("rho", Call("MulHom", V("S"), Endomorphism(V("W"))),
        All("n", N(), EqTo(Call("tensorAction", V("rho"), V("n")),
            LambdaOf(V("s"), V("S"),
                App(Qualified("PiTensorProduct", "map"),
                    LambdaOf(new Formula.Placeholder(), Call("Fin", V("n")), App(V("rho"), V("s")))))))))))))));

    private static Formula ClaimBody() =>
        All("k", V("Type"), All("S", V("Type"), All("V", V("Type"),
        Inst(Call("Field", V("k")), Inst(Call("IsAlgClosed", V("k")),
        Inst(Call("Semigroup", V("S")), Inst(Call("Fintype", V("S")),
        Inst(Call("Nonempty", V("S")), Inst(Call("AddCommGroup", V("V")),
        Inst(Call("Module", V("k"), V("V")), Inst(Call("FiniteDimensional", V("k"), V("V")),
        All("rho", Call("MulHom", V("S"), Endomorphism(V("V"))),
        ImpliesTo(new Formula.Not(Some("e", V("S"), All("s", V("S"),
            And(EqTo(Multiply(V("e"), V("s")), V("s")),
                EqTo(Multiply(V("s"), V("e")), V("s")))))),
        ImpliesTo(All("s", V("S"), new Formula.Not(Call("IsUnit", App(V("rho"), V("s"))))),
        And(Some("m", N(), And(LeTo(D(1), V("m")),
                Call("HasNullSummand", Call("tensorAction", V("rho"), V("m"))))),
        And(Some("b", Arrow(N(), N()), CountSequence()),
            All("b", Arrow(N(), N()), ImpliesTo(CountSequence(), Limit()))))))))))))))))));

    private static Formula CountSequence() =>
        All("n", N(), Call("IsSummandCount", Call("tensorAction", V("rho"), V("n")),
            App(V("b"), V("n"))));

    private static Formula Limit() => App(Qualified("Filter", "Tendsto"),
        LambdaOf(V("n"), N(), new Formula.Fraction(
            Coerce(App(V("b"), V("n")), R()),
            new Formula.Power(Coerce(Rank(V("V")), R()), V("n")))),
        Qualified("Filter", "atTop"), Call("nhds", D(1)));

    private static Formula Invariant(Formula p) => All("s", V("S"),
        Member(p, Seq(Parenthesized(App(V("a"), V("s"))), Dot, V("invtSubmodule"))));
    private static Formula Endomorphism(Formula w) => App(Qualified("Module", "End"), V("k"), w);
    private static Formula Subspace(Formula w) => Call("Submodule", V("k"), w);
    private static Formula Rank(Formula w) => App(Qualified("Module", "finrank"), V("k"), w);
    private static Formula V(string name) => F.Id(name);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula R() => Seq(Mathbb, Grp(V("R")));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Inst(Formula type, Formula body) => Seq(OpenBracket, type, CloseBracket, Sp, body);
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(domain, codomain);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula LambdaOf(Formula name, Formula type, Formula body) =>
        Seq(V("fun"), Sp, Parenthesized(Seq(name, Colon, Sp, type)), Sp, Mapsto, Sp, body);
    private static Formula Coerce(Formula value, Formula type) =>
        Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula ImpliesTo(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula IffTo(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula EqTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula NeTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula LeTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Multiply(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
}
