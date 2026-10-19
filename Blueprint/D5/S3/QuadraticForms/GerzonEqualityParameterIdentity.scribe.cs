using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class GerzonEqualityParameterIdentityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuadraticForms/GerzonEqualityParameterIdentity.";
    private const string Note = "D5/L/QuadraticForms/greavesiversonjaspermixon2021orthogonalframes";
    private const string Question = "Example 5.8, page 21: “The authors do not know how to construct an ETF with any of the parameters given in Table 4. In particular, every instance of Gerzon equality that we currently know satisfies the identity a² = (d + 2)b, but this equation does not occur anywhere in Table 4 (where b = 1). Proposition 2.10 implies that a² = (d + 2)b whenever Gerzon’s bound is saturated, d ≢ₚ 0, and d ≢ₚ 1. The authors do not know if these conditions can be removed.”";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At Gerzon equality, the equiangular parameters satisfy a² = (d + 2)b over every field of characteristic different from two and in every dimension at least two.",
        H("Gerzon equality without dimension congruence restrictions"),
        Blocks(
            Entry("gram-pair-sum", "gram_pair_sum", "Pairing a linear combination with an equiangular vector", GramPairSumFormula(),
                AssessedProvenance.FromRepo(),
                "A bilinear form with constant diagonal value a squared and constant off-diagonal value b pairs a linear combination with its j-th vector by separating the j-th coefficient from the sum of all coefficients. The scalar field and the module are arbitrary; neither symmetry nor nondegeneracy is needed.",
                DescribeRole.Theorem),
            Entry("equiangular-system", "IsEquiangularSystem", "Equiangular systems", EquiangularDefinition(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)),
                "Definition 2.8, page 5: “Let Φ = {ϕⱼ}ⱼ∈[n] be a sequence of vectors in a quadratic space W over F_q. For a, b ∈ F_q, Φ is called an (a, b)-equiangular system if: (i) ⟨ϕⱼ, ϕⱼ⟩ = a for every j ∈ [n], (ii) ⟨ϕᵢ, ϕⱼ⟩² = b for every i ≠ j in [n].” The sequence is represented by φ : Fin n → Fin d → F, the pairing by B, and the field parameters by a and b. Fin n indexes n vectors from zero; [n] in the paper indexes the same number from one. The predicate is polymorphic in the field and does not require its finiteness.",
                DescribeRole.Definition),
            Entry("claim", "claim", "The unrestricted parameter identity", Equal(Call("claim"), Parenthesized(ClaimBody())),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)),
                Question + " Here F is finite, ringChar F differs from two, d is any natural number at least two, and B is symmetric and nondegenerate. The number of vectors is exactly Nat.choose (d + 1) 2, the Gerzon bound of Proposition 2.9. The inequality a² ≠ b is retained. Casting d into F precedes field addition and multiplication. There is no restriction on d modulo the characteristic. Proposition 2.10 supplies the earlier ETF parameter equation, while this statement asks for the identity without the two dimension congruences.",
                DescribeRole.Definition),
            Entry("result", "result", "Gerzon equality fixes the parameters", Call("claim"),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                "The statement holds, including dimensions congruent to zero or one in the field. An orthogonal basis reduces the form to diagonal coordinates. The rank-one operators either form a basis of the selfadjoint-matrix space or span its trace-zero hyperplane. Their fourth-moment operator has the form α·id + β·tr·I; comparison of a diagonal matrix unit and a symmetric off-diagonal pair forces α = 2β. The resulting parameter equation uses no division by d or d − 1. The proof also works over infinite fields of characteristic different from two. Dimension one is excluded: with one vector the off-diagonal equation has no instances, so b can vary independently of a.",
                DescribeRole.Theorem))));

    private static Formula GramPairSumFormula()
    {
        var index = Call("Fin", V("n"));
        var gram = All(V("i"), index, All(V("j"), index,
            Equal(Call("K", Call("P", V("i")), Call("P", V("j"))),
                Call("if", Equal(V("i"), V("j")), Square(V("a")), V("b")))));
        var sum = Seq(new Formula.Subscript(Sum, Seq(V("i"), Colon, Sp, index)), Sp,
            Parenthesized(Call("smul", Call("t", V("i")), Call("P", V("i")))));
        var coefficients = Seq(new Formula.Subscript(Sum, Seq(V("i"), Colon, Sp, index)), Sp, Call("t", V("i")));
        var equation = Equal(Call("K", sum, Call("P", V("j"))),
            Add(Multiply(Parenthesized(Subtract(Square(V("a")), V("b"))), Call("t", V("j"))),
                Multiply(V("b"), Parenthesized(coefficients))));
        var body = All(V("K"), Apply(Qualified("LinearMap", "BilinForm"), V("F"), V("S")),
            All(V("P"), Arrow(index, V("S")), All(V("a"), V("F"), All(V("b"), V("F"),
                Imp(gram, All(V("t"), Arrow(index, V("F")), All(V("j"), index, equation)))))));
        var structures = Seq(OpenBracket, Call("Field", V("F")), CloseBracket, Sp,
            OpenBracket, Call("AddCommGroup", V("S")), CloseBracket, Sp,
            OpenBracket, Call("Module", V("F"), V("S")), CloseBracket, Sp, All(V("n"), Nat, body));
        var type = Seq(V("Type"), Star);
        return All(V("F"), type, All(V("S"), type, structures));
    }

    private static Formula EquiangularDefinition()
    {
        var self = All(V("j"), Call("Fin", V("n")), Equal(Pairing(V("j"), V("j")), V("a")));
        var off = All(V("i"), Call("Fin", V("n")), All(V("j"), Call("Fin", V("n")),
            Imp(NotEqual(V("i"), V("j")), Equal(Square(Pairing(V("i"), V("j"))), V("b")))));
        var body = Equal(Call("IsEquiangularSystem", V("B"), Varphi, V("a"), V("b")),
            Parenthesized(Seq(Parenthesized(self), Sp, Land, Sp, Parenthesized(off))));
        body = All(V("a"), V("F"), All(V("b"), V("F"), body));
        body = All(Varphi, Arrow(Call("Fin", V("n")), Vectors), body);
        body = All(V("B"), BilinearForm, body);
        body = All(V("d"), Nat, All(V("n"), Nat, body));
        return All(V("F"), Call("Type"), Instances(false, body));
    }

    private static Formula ClaimBody()
    {
        var equation = Equal(Square(V("a")), Seq(Parenthesized(Seq(
            Typed(V("d"), V("F")), Sp, Plus, Sp, D(2))), Sp, Cdot, Sp, V("b")));
        var body = Imp(Call("IsEquiangularSystem", V("B"), Varphi, V("a"), V("b")),
            Imp(NotEqual(Square(V("a")), V("b")), equation));
        body = All(V("a"), V("F"), All(V("b"), V("F"), body));
        body = All(Varphi, Arrow(Call("Fin", Count), Vectors), body);
        body = Imp(Property(V("B"), "IsSymm"), Imp(Property(V("B"), "Nondegenerate"), body));
        body = All(V("B"), BilinearForm, body);
        body = All(V("d"), Nat, Imp(Seq(D(2), Sp, Leq, Sp, V("d")), body));
        body = Imp(NotEqual(Call("ringChar", V("F")), D(2)), body);
        return All(V("F"), Call("Type"), Instances(true, body));
    }

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        AssessedProvenance provenance, string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role,
            name == "result" ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("greaves-iverson-jasper-mixon-2021-gerzon-equality-identity"),
                ResolutionKind.Proved) : null);

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Vectors => Arrow(Call("Fin", V("d")), V("F"));
    private static Formula BilinearForm => Apply(Qualified("LinearMap", "BilinForm"), V("F"), Vectors);
    private static Formula Count => Apply(Qualified("Nat", "choose"), Parenthesized(Seq(V("d"), Sp, Plus, Sp, D(1))), D(2));
    private static Formula Pairing(Formula i, Formula j) => Call("B", Apply(Varphi, i), Apply(Varphi, j));
    private static Formula Instances(bool finite, Formula body) => finite
        ? Seq(OpenBracket, Call("Field", V("F")), CloseBracket, Sp,
            OpenBracket, Call("Fintype", V("F")), CloseBracket, Sp, body)
        : Seq(OpenBracket, Call("Field", V("F")), CloseBracket, Sp, body);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula name, Formula type) => Parenthesized(Seq(name, Sp, Colon, Sp, type));
    private static Formula All(Formula name, Formula type, Formula body) => Seq(Forall, Sp, Typed(name, type), Comma, Sp, body);
    private static Formula Arrow(Formula domain, Formula codomain) => Parenthesized(Seq(domain, Sp, To, Sp, codomain));
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula NotEqual(Formula left, Formula right) => Seq(left, Sp, Neq, Sp, right);
    private static Formula Imp(Formula premise, Formula conclusion) => Seq(Parenthesized(premise), Sp, Rightarrow, Sp, Parenthesized(conclusion));
    private static Formula Square(Formula value) => new Formula.Power(value, D(2));
    private static Formula Property(Formula value, string member) => Seq(value, Dot, Call(member));
    private static Formula Qualified(string owner, string name) => Seq(Call(owner), Dot, Call(name));
    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? Seq(Operatorname, Grp(V(name)))
        : new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Apply(Formula function, params Formula[] args) => Seq(function, Parenthesized(Seq(
        [.. args.SelectMany((arg, index) => index == 0 ? new[] { arg } : new[] { Comma, Sp, arg })])));
}
