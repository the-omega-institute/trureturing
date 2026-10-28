using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HereditaryFlip;

internal sealed class MajorityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/HereditaryFlip/Majority.";
    private static readonly LibraryNoteRef Classical =
        LibraryNoteRef.Create("D5/L/GraphInvariants/betre2024pure");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hereditary families of finite supports are majority closed exactly when all empty, "
        + "singleton and pair constraints determine membership. Their pair completion is the "
        + "least majority-closed containing family.",
        H("Majority and flag completion"),
        Blocks(
            Paragraph(Text("Let V be any type with decidable equality. Supports are finite subsets "
                + "of V, and a family K is a set of such supports; V and K need not be finite. "
                + "Heredity means IsLowerSet K for inclusion of supports. The empty family is "
                + "allowed. Every nonempty hereditary family contains the empty support.")),
            Node("majority", "Support majority", "majority",
                Eq(Call("majority", Id("A"), Id("B"), Id("C")),
                    Call("union", Call("union", Call("intersection", Id("A"), Id("B")),
                        Call("intersection", Id("B"), Id("C"))),
                        Call("intersection", Id("C"), Id("A")))),
                "A vertex occurs in the majority exactly when at least two inputs contain it.",
                DescribeRole.Definition, false),
            Node("majority-closed", "Majority closure", "MajorityClosed",
                Iff(Call("MajorityClosed", Id("K")),
                    All("A", Supports(), All("B", Supports(), All("C", Supports(),
                        Imp(And(Member(Id("A"), Id("K")),
                            And(Member(Id("B"), Id("K")), Member(Id("C"), Id("K")))),
                            Member(Call("majority", Id("A"), Id("B"), Id("C")), Id("K"))))))),
                "All three inputs and the majority belong to the same family.",
                DescribeRole.Definition, false),
            Node("flag", "All small faces determine membership", "Flag",
                Iff(Call("Flag", Id("K")), All("S", Supports(),
                    Imp(SmallFaces(Id("K"), Id("S")), Member(Id("S"), Id("K"))))),
                "SmallFaces(K,S) means that every T contained in S with cardinality at most two "
                + "belongs to K. This includes the empty support and singletons. A vertex whose "
                + "singleton is absent cannot appear in a completed face.",
                DescribeRole.Definition, false),
            Node("pair-completion", "Completion from small faces", "pairClosure",
                All("S", Supports(), Iff(Member(Id("S"), Call("pairClosure", Id("K"))),
                    SmallFaces(Id("K"), Id("S")))),
                "The completion keeps exactly the finite supports satisfying all original "
                + "empty, singleton and pair constraints.", DescribeRole.Definition, false),
            Node("majority-flag", "Hereditary majority closure is flagness", "majority_closed_iff_flag",
                All("K", Families(), Imp(Call("IsLowerSet", Id("K")),
                    Iff(Call("MajorityClosed", Id("K")), Call("Flag", Id("K"))))),
                "For a hereditary K, majority closure and flagness are equivalent. In a majority, "
                + "every subset of size at most two is contained in a common supporting input: "
                + "two subsets of the three input positions, each of size at least two, intersect. "
                + "Heredity makes that small subset legal, and flagness makes the majority legal. "
                + "Conversely, use strong induction on a support S satisfying all small constraints. "
                + "The case of size at most two is immediate. Otherwise choose three distinct "
                + "vertices a,b,c. The three erased supports are smaller, satisfy the same local "
                + "constraints and belong to K inductively. Their majority is S. Heredity alone "
                + "does not guarantee majority closure: the three edges of a triangle belong to "
                + "its boundary, while their majority is the missing triangle. The finite version "
                + "is classical; the statement here permits arbitrary ambient types and absent vertices.",
                DescribeRole.Theorem, true),
            Node("least-completion", "Least majority-closed extension", "pair_closure_is_least",
                All("K", Families(), Imp(Call("IsLowerSet", Id("K")),
                    Call("IsLeast", Call("majorityClosedExtensions", Id("K")),
                        Call("pairClosure", Id("K"))))),
                "The extensions are all families L with K contained in L and MajorityClosed L. "
                + "Pair completion contains K, is hereditary and is flag, hence is majority closed. "
                + "For universal minimality, L is not assumed hereditary. Strong induction on the "
                + "cardinality of S in pairClosure K starts with S in K for cardinality at most two. "
                + "In larger cardinalities, the same three erased faces lie in L inductively, "
                + "and their majority reconstructs S. Thus pairClosure K is contained in every "
                + "such L. This is a consequence of the small-face induction, with no claim of "
                + "new mathematical novelty. No graph distance or metric median assertion is made.",
                DescribeRole.Theorem, false))));

    private static DocumentBlock Node(string id, string title, string name, Formula formula,
        string prose, DescribeRole role, bool classical) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), classical
                ? AssessedProvenance.FromLiterature(Classical) : AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
    private static Formula Id(string name) => F.Id(name);
    private static Formula Supports() => Call("Finset", Id("V"));
    private static Formula Families() => Call("Set", Supports());
    private static Formula All(string x, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), t, b);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Member(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(Seq(Open, a, Close), FormulaLogicOperator.Iff, Seq(Open, b, Close));
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Seq(Open, a, Close), FormulaLogicOperator.And, Seq(Open, b, Close));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Seq(Open, a, Close), FormulaLogicOperator.Implies, Seq(Open, b, Close));
    private static Formula SmallFaces(Formula k, Formula s) => All("T", Supports(),
        Imp(And(new Formula.Relation(Id("T"), FormulaRelationOperator.SubsetOf, s),
            new Formula.Relation(Call("card", Id("T")),
                FormulaRelationOperator.LessThanOrEqual, D(2))), Member(Id("T"), k)));
}
