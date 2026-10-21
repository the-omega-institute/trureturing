using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class AliabadiZerbibMatroidMatchingDocument : IScribeDocumentDefinition
{
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Geometry/aliabadizerbib2024matroidmatching");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A sparse paving integer matroid need not be matched to itself.",
        H("Aliabadi–Zerbib matroid matching"),
        Blocks(
            Node("IsPaving", GroupFree(All("M", Call("Matroid", V("G")),
                IffFormula(Call("IsPaving", V("M")), All("X", Call("Set", V("G")),
                    Imp(Rel(V("X"), FormulaRelationOperator.SubsetOf, Q("M", "E")),
                        Imp(Equal(Add(Q("X", "encard"), D(1)), Q("M", "eRank")),
                            App(Q("M", "Indep"), V("X")))))))),
                AssessedProvenance.FromLiterature(Source),
                "Page 2: “A matroid M = (E, I) of rank n is said to be a paving matroid if every (n − 1)-subset of E is independent.” Here X is a ground subset, X.encard is its extended natural cardinality and M.eRank is the extended natural rank; the size condition is X.encard + 1 = M.eRank.",
                DescribeRole.Definition),
            Node("IsSparsePaving", GroupFree(All("M", Call("Matroid", V("G")),
                IffFormula(Call("IsSparsePaving", V("M")),
                    And(Call("IsPaving", V("M")), Call("IsPaving", Dual(V("M"))))))),
                AssessedProvenance.FromLiterature(Source),
                "Page 2: “If M and M* are both paving matroids then M is called a sparse paving matroid.” The star is Mathlib's matroid dual.",
                DescribeRole.Definition),
            Node("BasesMatched", Grouped(All("M", Call("Matroid", V("G")), All("n", Nat,
                All("a", Arrow(Call("Fin", V("n")), V("G")),
                    All("b", Arrow(Call("Fin", V("n")), V("G")),
                        IffFormula(Call("BasesMatched", V("M"), V("a"), V("b")),
                            All("i", Call("Fin", V("n")),
                                NotIn(Add(App(V("a"), V("i")), App(V("b"), V("i"))), Q("M", "E"))))))))),
                AssessedProvenance.FromLiterature(Source),
                "Page 2, Definition 1.3(1): “Let M and N be two matroids over G with r(M) = r(N) = n > 0. Let M = {a₁, . . . , aₙ} and N = {b₁, . . . , bₙ} be ordered bases of M and N, respectively. We say M is matched to N if aᵢ + bᵢ ∉ E(M), for all 1 ≤ i ≤ n.” Indices are Fin n. This predicate is the sum-exclusion clause; IsMatchedTo also requires injectivity and the two basis conditions.",
                DescribeRole.Definition),
            Node("IsMatchedTo", Grouped(All("M", Call("Matroid", V("G")),
                All("N", Call("Matroid", V("G")),
                    IffFormula(Call("IsMatchedTo", V("M"), V("N")), MatchedBody())))),
                AssessedProvenance.FromLiterature(Source),
                "Page 2, Definition 1.3(2): “We say that M is matched to N if for every basis M of M there exists a basis N of N, so that M is matched to N.” An ordered basis is an injective Fin n enumeration whose Set.range is a Mathlib base. The existential ordering of the target includes all possible permutations.",
                DescribeRole.Definition),
            Node("claim", IffFormula(V("claim"), ClaimBody()),
                AssessedProvenance.FromLiterature(Source),
                "Page 5, Question 2.7: “Let G be an abelian torsion-free group. Let M be a matroid over G and N be a sparse paving matroid over G, both of the same rank n, so that |E(M)| = |E(N)| − 1 or |E(M)| = |E(N)|. If 0 ∉ E(N), is M matched to N?” The proposition is the positive answer in the paper's standing finite, loopless setting, with positive common rank. The first size alternative uses addition of one to the smaller cardinality. IsAddTorsionFree is Mathlib's additive torsion-free class.",
                DescribeRole.Definition),
            Node("result", Seq(Neg, Sp, Parenthesized(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                "Over ℤ, let E = {1, …, n + s} and H = {s + 1, …, s + n}, with n, s ≥ 2. The bases are exactly the n-element subsets of E other than H. A two-exchange argument constructs a matroid; extension of smaller sets and complementary bases show that it and its dual are paving. For a in {1, …, n}, b in E and a + b outside E, one has b in H. Thus an injective n-tuple of targets has range H, which is not a base. Taking M = N at n = s = 2 disproves the proposition.",
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, Formula formula, AssessedProvenance provenance,
        string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create(name.ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching." + name),
            H(name), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula MatchedBody()
    {
        var target = Some("b", Arrow(Call("Fin", V("n")), V("G")),
            And(App(Q("Function", "Injective"), V("b")),
                And(App(Q("N", "IsBase"), App(Q("Set", "range"), V("b"))),
                    Call("BasesMatched", V("M"), V("a"), V("b")))));
        return All("n", Nat, All("a", Arrow(Call("Fin", V("n")), V("G")),
            Imp(App(Q("Function", "Injective"), V("a")),
                Imp(App(Q("M", "IsBase"), App(Q("Set", "range"), V("a"))), target))));
    }

    private static Formula ClaimBody()
    {
        var sizes = Or(
            Equal(Add(App(Q("Set", "ncard"), Q("M", "E")), D(1)), App(Q("Set", "ncard"), Q("N", "E"))),
            Equal(App(Q("Set", "ncard"), Q("M", "E")), App(Q("Set", "ncard"), Q("N", "E"))));
        var answer = Imp(NotIn(Parenthesized(Seq(D(0), Colon, Sp, V("G"))), Q("N", "E")),
            Call("IsMatchedTo", V("M"), V("N")));
        answer = Imp(sizes, answer);
        answer = Imp(Call("IsSparsePaving", V("N")), answer);
        answer = Imp(Equal(Q("M", "eRank"), Q("N", "eRank")), answer);
        answer = Imp(Rel(D(0), FormulaRelationOperator.LessThan, Q("M", "eRank")), answer);
        answer = Imp(Q("N", "Loopless"), answer);
        answer = Imp(Q("M", "Loopless"), answer);
        answer = Imp(Q("N", "Finite"), answer);
        answer = Imp(Q("M", "Finite"), answer);
        return All("G", V("Type"), Seq(Instance("AddCommGroup"), Sp, Instance("IsAddTorsionFree"), Sp,
            All("M", Call("Matroid", V("G")), All("N", Call("Matroid", V("G")), answer))));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Q(string owner, string name) =>
        Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula App(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => App(V(name), arguments);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula GroupFree(Formula body) => All("G", V("Type"), body);
    private static Formula Grouped(Formula body) => GroupFree(Seq(Instance("AddCommGroup"), Sp, body));
    private static Formula Instance(string name) => Seq(OpenBracket, Call(name, V("G")), CloseBracket);
    private static Formula Dual(Formula value) => new Formula.Power(value, Star);
    private static Formula Add(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula NotIn(Formula a, Formula b) => Seq(Neg, Sp, Parenthesized(Rel(a, FormulaRelationOperator.MemberOf, b)));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula IffFormula(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
}
