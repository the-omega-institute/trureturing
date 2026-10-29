using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates.Algebra;

internal sealed class WangConjecture326RefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/Algebra/WangConjecture326Refutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/wang2025semigrouprings");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One infinite commutative periodic semigroup over Q has algebraic Davenport "
            + "constant at most one and unbounded relative constants in its actual Green quotient.",
        H("Wang Conjecture 3.26: an Infinite Ordinary Semigroup Algebra Counterexample"),
        Blocks(
            Node("positive-cyclic", "cyclic", "Positive cyclic generation",
                "Use the native additive subsemigroup closure of {a}, containing positive "
                    + "sums only. No identity or zeroth multiple is adjoined."),
            Node("pointwise-periodicity", "Periodic", "Pointwise periodicity",
                "Every individual cyclic closure is finite. There is no Finite S or "
                    + "Fintype S hypothesis, so the statement includes infinite semigroups."),
            Node("idempotent-spec", "IsCyclicIdempotent", "Actual cyclic idempotency",
                "The selected element belongs to the positive cyclic subsemigroup and satisfies e+e=e."),
            Node("idempotent-choice", "cyclicIdempotent", "Cyclic idempotent selection",
                "Select an idempotent in the cyclic closure. Under pointwise periodicity "
                    + "Mathlib's compact-subsemigroup theorem proves existence using only the "
                    + "finite cyclic set with the discrete topology. The fallback is unreachable. "
                    + "The witness calculation identifies this choice with its unique cyclic idempotent."),
            Node("cyclic-group", "CyclicIsGroup", "A positive cyclic group with its own identity",
                "Quantify an identity and inverses inside the actual positive cyclic subsemigroup. "
                    + "The identity need not equal an ambient monoid identity."),
            Node("ordinary-factor", "factor", "The full ordinary convolution algebra",
                "The factor is single(a,1)-single(e(a),c) in upstream AddMonoidAlgebra R S. "
                    + "R is any commutative unitary ring. Every label, including level two, is retained."),
            Node("positive-product", "factorProduct", "Positive products without an algebra unit",
                "For a nonempty list start with its first factor and fold multiplication over "
                    + "the indexed tail. Each coefficient uses its own original position. The "
                    + "empty branch is zero, contributing only zero to the length supremum."),
            Node("positional-coefficients", "GoodSequence", "Every independently nonzero coefficient tuple",
                "Quantify c:N->R and require c(i) nonzero at every occupied position. Values "
                    + "outside the finite prefix are unused. Equal labels retain distinct positions."),
            Node("algebraic-constant", "algebraicD", "The algebraic Davenport constant",
                "The ENat supremum is taken over all finite good sequence lengths. Top means "
                    + "unbounded finite lengths, without an infinite product."),
            Node("principal-ideal", "principalIdeal", "Actual principal ideals",
                "The principal ideal contains a itself and every a+c for c in S, with no "
                    + "artificial identity. In the witness membership is A subset B and k<=l."),
            Node("green-quotient", "greenCon", "The actual Green congruence",
                "The relation is equality of principal ideals. Compatibility with addition is "
                    + "proved in the definition. Use the native AddCon quotient and quotient map."),
            Node("sequence-sum", "SequenceSum", "Sums including the empty subsequence",
                "Nonempty lists sum by folding the semigroup operation. Empty lists sum only "
                    + "to an existing two-sided identity. For any monoid this is equivalent to List.sum."),
            Node("relative-irreducibility", "IrreducibleAt", "Irreducibility at a specified sum",
                "The list sums to a, and no shorter sublist has that sum, including the empty "
                    + "sublist. Lists enumerate unordered source sequences in a commutative semigroup."),
            Node("relative-constant", "relativeD", "The relative Davenport constant",
                "Take the ENat supremum of all irreducible lengths at the specified element."),
            Node("filtered-supremum", "nongroupSup", "The source's uniform filtered supremum",
                "Take one supremum over all a whose positive cyclic subsemigroup is not a group, "
                    + "using relativeD at the actual canonical quotient image of a."),
            Describe.Lean(DescribeId.Create("whole-published-claim"),
                DeclarationHandle.Create(Prefix + "claim"), H("The complete published universal implication"),
                StatementSource.FromAuthor(ClaimFormula()), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Every commutative semigroup, including infinite and nonunital ones, is in "
                    + "scope. Periodic means pointwise finite positive cyclic closure. R ranges "
                    + "over every commutative unitary ring, with no field or nontriviality "
                    + "restriction. The antecedent is finiteness of the ordinary algebraic constant; "
                    + "the consequent is one uniform finite bound on the source's filtered "
                    + "relative constants. The closed Prop uses ordinary small carriers."))), DescribeRole.Definition),
            Node("infinite-carrier", "Model", "One fixed infinite carrier",
                "The carrier is Finset(N) times Fin 3. The map i maps to ({i},0) is injective, "
                    + "giving an Infinite instance. No finite truncation replaces this carrier."),
            Node("capped-addition", "modelAdd", "Union and min-capped addition",
                "Add (A,k) and (B,l) as (A union B,min(2,k+l)). The Fin 3 levels use this "
                    + "custom min-cap operation, never modular addition. The identity is (empty,0)."),
            Node("model-idempotent", "modelE", "The witness cyclic idempotent",
                "Retain the finite subset; level zero remains zero, and positive levels go "
                    + "to level two. The positive cyclic closure is exactly {x,E(x)}."),
            Node("subadditive-weight", "weight", "A weight detecting relative length",
                "Set w(A,k)=card(A)+1(k!=0). Union cardinality and the nonzero-level indicator "
                    + "make this weight subadditive. It bounds the weight of a sum by the "
                    + "length of any sequence whose terms all have weight one."),
            Node("unbounded-sequences", "witnessSequence", "One sequence for every natural n",
                "Start with (empty,1), then add one term ({i},0) for each i<n. Each term "
                    + "has weight one. The length is n+1 and the sum is target(n)."),
            Node("unbounded-targets", "target", "The targets inside the same semigroup",
                "The target is (range(n),1). Its weight is n+1. Its two-element positive cyclic "
                    + "subsemigroup has no identity of its own, so it satisfies the nongroup filter."),
            Describe.Lean(DescribeId.Create("conjecture-three-twenty-six-refuted"),
                DeclarationHandle.Create(Prefix + "result"), H("Conjecture 3.26 is false"),
                StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Over Q the all-ones coefficient assignment kills every sequence of length "
                    + "at least two. An idempotent gives a zero factor; two level-one terms "
                    + "give four coincident basis products whose coefficients cancel. Thus "
                    + "algebraicD(Model,Q)<=1. Principal ideals distinguish every model element, "
                    + "so the actual Green quotient map is injective. Every subsequence of "
                    + "witnessSequence(n) with sum target(n) has at least n+1 terms by the "
                    + "subadditive weight, proving quotient irreducibility. Every target is "
                    + "cyclic nongroup, and its relative constant is at least n+1. The filtered "
                    + "supremum is therefore top inside this single infinite periodic semigroup. "
                    + "This negates the entire original implication. Exact individual constants, "
                    + "novelty, priority, and the separate Conjecture 5.3 are not conclusions "
                    + "of this theorem."))), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("wang-conjecture326"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Named(string x) => Seq(Operatorname, Grp(F.Id(x)));
    private static Formula Call(string name, params Formula[] args)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var arg in args) { if (items.Count != 0) items.Add(Comma); items.Add(arg); }
        return Seq(Named(name), Par(Seq([.. items])));
    }
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Par(Seq(F.Id(name), Colon, type)), Comma, Sp, body);
    private static Formula Instance(string name, Formula carrier, Formula body) =>
        Seq(OpenBracket, Call(name, carrier), CloseBracket, Sp, body);
    private static Formula LtTop(Formula x) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThan, Named("top"));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula ClaimFormula()
    {
        var s = F.Id("S"); var r = F.Id("R");
        var body = All("S", Named("Type"), Instance("AddCommSemigroup", s,
            Imp(Call("Periodic", s), All("R", Named("Type"), Instance("CommRing", r,
                Imp(LtTop(Call("algebraicD", s, r)), LtTop(Call("nongroupSup", s))))))));
        return Disp(new Formula.Logic(Seq(F.Id("claim"), Colon, Named("Prop")),
            FormulaLogicOperator.Iff, body));
    }
}
