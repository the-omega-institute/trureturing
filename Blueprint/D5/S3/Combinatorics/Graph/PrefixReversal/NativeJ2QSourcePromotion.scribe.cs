using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeJ2QSourcePromotionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2QSourcePromotion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original retained suppliers and their actual saved parent determine the path inventories.",
        H("Actual Saved Native Suppliers"),
        Blocks(
            Item("native_j2_same_q_three_fragments", "Split the Exact Saved Q Opening into Three Paths", Outer(Call("SameQOpeningThreeFragments", F.Id("parent"))),
                "For every saved OuterParentWitnessFor W in the same range, use joint pieces 5, 4 and reversed 1 of its retained Q seed to recover the middle E2 path. The actual ordered special path in W is cut at the two new index-zero marked edges. The resulting three simple paths have endpoints R0 to new primary L0, new primary R0 to new opposite L0, and new opposite R0 to old L2. Their concatenated support equals W.special.path.support exactly. Re-inserting the two actual cut edges recovers its complete edge list, and omitting them is exactly the filtered edge list. The primary new frame is nextFrame(reverseSelected F), while the opposite is nextFrame F. This conclusion is about W.special.path, not a newly selected special child."))));

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
