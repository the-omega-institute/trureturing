using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeJ2JointPromotionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2JointPromotion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original retained suppliers and their actual saved parent determine the path inventories.",
        H("Actual Saved Native Suppliers"),
        Blocks(
            Item("native_j2_same_parent_eight_piece_partition", "Earn the Eight Actual Third-Order Joint Pieces on the Same Parent", Outer(Call("SameParentEightPiecePartition", F.Id("parent"))),
                "For every m at least five, every old two-label frame F with base A appended by u and A of length at least three, and every saved OuterParentWitnessFor W, construct eight genuine paths on its independently defined outer parent domain. Their order is reversed new piece 0, new piece 1, new piece 2, old P pieces 4, 3, 2, 0 and 5. For N0 = nextFrame(reverseSelected F) and N1 = nextFrame F, their oriented endpoints are respectively (L N0 0,L N0 2), (R N0 0,L N1 0), (R N1 0,L N1 1), (R N0 1,R N0 2), (L N1 3,R N0 3), (R N1 2,L N0 3), (R N1 1,R N1 3), and (L N1 2,L N0 1). Two disjoint actual cut sets map exactly to the marked cuts of N0 and N1. These pieces form ActualCyclePartition of the same W.cycle: their full support is a permutation of its tail support, their edges are a permutation of its edges outside the cut union, and every cut belongs to this cycle. No replacement parent or abstract target-partition certificate is assumed. The complete strong k3 state and all-size induction are further consumers; this theorem alone does not assert all-n Hamiltonicity."))));

    private static Formula Outer(Formula body) => Disp(All("m", Call("Nat"),
        Implies(Le(D(5), F.Id("m")), All("frame", Call("SupplyFrame", F.Id("m"), D(2)),
            All("A", Call("LabelList", F.Id("m")), All("u", Call("Label", F.Id("m")),
                Implies(And(Eq(Call("Base", F.Id("frame")),
                    Call("Append", F.Id("A"), Call("Singleton", F.Id("u")))),
                    Le(D(3), Call("Length", F.Id("A")))),
                    All("parent", Call("OuterParentWitnessFor", F.Id("m"), F.Id("frame"),
                        F.Id("A"), F.Id("u")), body))))))));

    private static DocumentBlock Item(string name, string title, Formula formula, string meaning) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(meaning))), DescribeRole.Theorem);
    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}
