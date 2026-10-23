using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeJ2SourcePromotionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2SourcePromotion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original retained suppliers and their actual saved parent determine the path inventories.",
        H("Actual Saved Native Suppliers"),
        Blocks(
            Item("native_j2_original_p_opening_inventory", "The Original P Opening Keeps Its Actual Joint Inventory", Outer(Call("OriginalPOpeningInventory", F.Id("parent"))),
                "For every m at least five, every two-label frame F with base A appended by u and A of length at least three, and every saved OuterParentWitnessFor W, the final ordinary opening of W has precisely the full joint support of W.P. Its edges are a permutation of the same retained P cycle after removing the literal supplier cut at the outer final base gap. Restoring the two original marked groups before filtering gives the same remaining-edge inventory. Neither the original P supplier nor the assembled parent cycle is replaced."),
            Item("native_j2_original_p_joint_split", "Earn the Actual Original P Prefix and Remaining Edges", Outer(Call("OriginalPJointPrefixSplit", F.Id("parent"))),
                "For the same W, joint piece 1 of the original P seed begins with an actual a edge and then the particular b edge deleted by its final-child opening. Their intermediate vertices are exactly the right and left outer ports at index m minus one. The remaining tail is an actual path. The final opening support is a permutation of this distinguished joint path and the other five saved joint paths; its remaining edges are those of the other paths, the tail, the first a edge, and both original marked groups. This inventory is consumed by NativeJ2JointPromotion for this same W.cycle, rather than frozen merely as a record of an application."))));

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
