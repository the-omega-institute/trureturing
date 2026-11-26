using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class AnholcerEpistemicEF1RefutationDocument : IScribeDocumentDefinition
{
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/FiniteGeometry/anholcer2026epistemic");
    private const string ConjectureQuote = "Page 21, Conjecture 4: “Let M₁, …, Mₙ be a collection of matroids on the same ground set E satisfying χ(Mᵢ) ⩽ n, for all i = 1, 2, …, n. Suppose that there are n agents with additive valuations v₁, …, vₙ of the set of goods (or chores) E. Then there exists an EF1 partition E = X₁ ∪ ··· ∪ Xₙ such that each set Xᵢ is independent in the matroid Mᵢ, for all i = 1, 2, …, n.”";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two heterogeneous two-colorable matroids on four items admit no goods-EF1 or chores-EF1 feasible partition.",
        H("Anholcer–Bartkowiak–Bosek–Grytczuk Conjecture 4"), Blocks(
            Node("IsPartition", MN(All("X", Bundles(V("m"), V("n")),
                EquivFormula(Call("IsPartition", V("X")), PartitionBody()))),
                AssessedProvenance.FromLiterature(Source),
                "Page 4: “Throughout, a partition into n bundles means an ordered n-tuple of pairwise disjoint, possibly empty, sets whose union is the relevant ground set.” Fin m enumerates the items and Fin n enumerates the agents, starting at zero. Completeness includes every item exactly once; empty bundles are allowed.", DescribeRole.Definition),
            Node("IndependentPartition", All("m", Nat, All("q", Nat,
                All("M", Matroid(V("m")), All("X", Bundles(V("m"), V("q")),
                    EquivFormula(Call("IndependentPartition", V("M"), V("X")),
                        And(Call("IsPartition", V("X")), All("i", Fin(V("q")),
                            App(Q("M", "Indep"), AsSet(App(V("X"), V("i"))))))))))),
                AssessedProvenance.FromLiterature(Source),
                "Page 5: “For a given independence structure M, we denote by χ(M) the chromatic number of M, that is, the least number of parts in a partition of the ground set E into independent sets.” The q bundles are independent in the same native Matroid. Each finite bundle is coerced to a Set.", DescribeRole.Definition),
            Node("chromaticNumber", All("m", Nat, All("M", Matroid(V("m")),
                Equal(Call("chromaticNumber", V("M")), ChromaticBody()))),
                AssessedProvenance.FromLiterature(Source),
                "Page 5: “For a given independence structure M, we denote by χ(M) the chromatic number of M, that is, the least number of parts in a partition of the ground set E into independent sets.” The infimum is in ℕ∞. An empty set of finite color counts has infimum infinity; the empty ground has color count zero. The hypotheses in claim require M.E = Set.univ.", DescribeRole.Definition),
            Node("Feasible", MN(All("M", Arrow(Fin(V("n")), Matroid(V("m"))),
                All("X", Bundles(V("m"), V("n")),
                    EquivFormula(Call("Feasible", V("M"), V("X")),
                        And(Call("IsPartition", V("X")), All("i", Fin(V("n")),
                            App(Q("Matroid", "Indep"), App(V("M"), V("i")), AsSet(App(V("X"), V("i")))))))))),
                AssessedProvenance.FromLiterature(Source),
                "Page 21: “Then there exists an EF1 partition E = X₁ ∪ ··· ∪ Xₙ such that each set Xᵢ is independent in the matroid Mᵢ, for all i = 1, 2, …, n.” Each bundle is tested in its own agent's Matroid. The ordered partition is complete.", DescribeRole.Definition),
            Node("value", MN(All("w", Weights(), All("i", Fin(V("n")),
                All("S", Call("Finset", Fin(V("m"))),
                    Equal(Call("value", V("w"), V("i"), V("S")),
                        Seq(new Formula.Subscript(Sum, Member(V("e"), V("S"))), Sp,
                            App(V("w"), V("i"), V("e")))))))),
                AssessedProvenance.FromLiterature(Source),
                "Page 4: “In this way, any subset of goods X ⊆ E, called a bundle, gets a value vᵢ(X) = ∑_{gⱼ∈X} vᵢ(gⱼ) given by agent i. Such valuations are called additive.” The singleton weights lie in NNReal, so the finite sum is nonnegative. No restriction to identical or strictly positive weights is imposed.", DescribeRole.Definition),
            Node("GoodsEF1", MN(All("w", Weights(), All("X", Bundles(V("m"), V("n")),
                EquivFormula(Call("GoodsEF1", V("w"), V("X")), GoodsBody())))),
                AssessedProvenance.FromLiterature(Source),
                "Page 4: “For general monotone valuations, we use the existential version: if Xⱼ ≠ ∅, there must exist a good g ∈ Xⱼ such that vᵢ(Xᵢ) ⩾ vᵢ(Xⱼ ∖ {g}); if Xⱼ = ∅, the condition is automatic.” This existential deletion formula also expresses additive EF1: a maximum-valued good minimizes the remaining value. The deletion is from the other agent's bundle, and the inequality compares its remaining value with the envying agent's entire bundle.", DescribeRole.Definition),
            Node("ChoresEF1", MN(All("w", Weights(), All("X", Bundles(V("m"), V("n")),
                EquivFormula(Call("ChoresEF1", V("w"), V("X")), ChoresBody())))),
                AssessedProvenance.FromLiterature(Source),
                "Page 20: “More formally, the allocation (X₁, …, Xₙ) is EF1 for chores if for every pair i ≠ j, either Xᵢ = ∅, or there exists a chore c ∈ Xᵢ such that vᵢ(Xᵢ ∖ {c}) ⩽ vᵢ(Xⱼ).” Only distinct agents are compared. Deletion is from the envying agent's own bundle.", DescribeRole.Definition),
            Node("claim", EquivFormula(V("claim"), ClaimBody()),
                AssessedProvenance.FromLiterature(Source),
                ConjectureQuote + " The carrier is Fin m, the number n of agents is positive, every matroid has ground Set.univ, and the singleton weights are arbitrary NNReal values. The goods and chores existentials may use different allocations. This is ordinary EF1; no imaginary allocation is quantified.", DescribeRole.Definition),
            Node("result", Not(ClaimBody()), AssessedProvenance.FromRepo(Source),
                "Take four items and two agents. The first matroid has capacity-one blocks {0,1} and {2,3}; the second has blocks {1,2} and {3,0}. Both admit the two-color partition {0,2}, {1,3}. A finite certificate shows that every complete feasible allocation is one of its two orders. Both agents assign weights (3,1,3,1). The two bundle values are 6 and 2, and every deletion from the high bundle leaves 3 > 2. Thus neither order satisfies goods-EF1 or chores-EF1. The heterogeneous constraints realize a complementary-item obstruction; Dror–Feldman–Segal-Halevi, JAIR 76 (2023), Section 8.3, supplies the earlier common-nonmatroid obstruction. The common-matroid conjectures and the epistemic variants remain outside this conclusion.", DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("op-abbg2606c4"), ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string name, Formula formula, AssessedProvenance provenance,
        string prose, DescribeRole role, OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(name.ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Combinatorics/Matroids/AnholcerEpistemicEF1Refutation." + name),
            H(name), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula PartitionBody() => And(
        All("i", Fin(V("n")), All("j", Fin(V("n")),
            Imp(NotEqual(V("i"), V("j")), Call("Disjoint", App(V("X"), V("i")), App(V("X"), V("j")))))),
        All("e", Fin(V("m")), Some("i", Fin(V("n")), Member(V("e"), App(V("X"), V("i"))))));

    private static Formula ChromaticBody()
    {
        var condition = Some("q", Nat, And(Equal(V("c"), Cast(V("q"), NatInfinity)),
            Some("X", Bundles(V("m"), V("q")), Call("IndependentPartition", V("M"), V("X")))));
        return Call("sInf", Seq(OpenBrace, V("c"), Colon, Sp, NatInfinity, Sp, Mid, Sp, condition, CloseBrace));
    }

    private static Formula GoodsBody() => All("i", Fin(V("n")), All("j", Fin(V("n")),
        Or(Equal(App(V("X"), V("j")), Emptyset),
            Some("g", Fin(V("m")), And(Member(V("g"), App(V("X"), V("j"))),
                LeFormula(Call("value", V("w"), V("i"), Delete(App(V("X"), V("j")), V("g"))),
                    Call("value", V("w"), V("i"), App(V("X"), V("i")))))))));

    private static Formula ChoresBody() => All("i", Fin(V("n")), All("j", Fin(V("n")),
        Imp(NotEqual(V("i"), V("j")), Or(Equal(App(V("X"), V("i")), Emptyset),
            Some("c", Fin(V("m")), And(Member(V("c"), App(V("X"), V("i"))),
                LeFormula(Call("value", V("w"), V("i"), Delete(App(V("X"), V("i")), V("c"))),
                    Call("value", V("w"), V("i"), App(V("X"), V("j"))))))))));

    private static Formula ClaimBody()
    {
        Formula existence(string fairness) => Some("X", Bundles(V("m"), V("n")),
            And(Call("Feasible", V("M"), V("X")), Call(fairness, V("w"), V("X"))));
        var body = All("w", Weights(), And(existence("GoodsEF1"), existence("ChoresEF1")));
        body = Imp(All("i", Fin(V("n")), LeFormula(Call("chromaticNumber", App(V("M"), V("i"))), Cast(V("n"), NatInfinity))), body);
        body = Imp(All("i", Fin(V("n")), Equal(App(Q("Matroid", "E"), App(V("M"), V("i"))), Q("Set", "univ"))), body);
        body = All("M", Arrow(Fin(V("n")), Matroid(V("m"))), body);
        return MN(Imp(new Formula.Relation(D(0), FormulaRelationOperator.LessThan, V("n")), body));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula NatInfinity => new Formula.Power(Nat, Infty);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Matroid(Formula m) => Call("Matroid", Fin(m));
    private static Formula Bundles(Formula m, Formula n) => Arrow(Fin(n), Call("Finset", Fin(m)));
    private static Formula Weights() => Arrow(Fin(V("n")), Arrow(Fin(V("m")), V("NNReal")));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(V(name), args);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula AsSet(Formula bundle) => Cast(bundle, Call("Set", Fin(V("m"))));
    private static Formula Delete(Formula bundle, Formula item) => App(Q("Finset", "sdiff"), bundle, new Formula.SetLiteral([item]));
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) => Seq(Exists, Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula MN(Formula body) => All("m", Nat, All("n", Nat, body));
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula LeFormula(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula EquivFormula(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Not(Formula body) => Seq(Neg, Sp, Parenthesized(body));
}
