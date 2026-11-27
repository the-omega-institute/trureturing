using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.UnorderedTrees;

internal sealed class LeafPruningDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/UnorderedTrees/LeafPruning.";
    private static Formula T => F.Id("T");
    private static Formula RootInternal => Call("Internal", T, Call("root", T));
    private static Formula Core => Seq(OpenBrace, F.Id("v"), Colon, Sp, F.Id("V"), Sp, Mid,
        Sp, Call("Internal", T, F.Id("v")), CloseBrace);
    private static Formula Pruned => Call("prune", T, F.Id("hr"));
    private static Formula SizeEquality => Eqn(Call("height", T), Call("internalCount", T));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Deleting all original leaves of a finite rooted tree with an internal root leaves the actual internal-vertex subtree and lowers vertex-height by one.",
        H("Leaf pruning of actual rooted trees"),
        Blocks(
            Node("prune", "The internal-vertex subtree", "prune",
                WithRoot(new Formula.Relation(Pruned, FormulaRelationOperator.MemberOf, Call("Tree", Core))),
                "The parent map restricts to the original internal vertices and fixes the original root. Parent iteration commutes with subtype inclusion, so retained vertices still reach the root.",
                DescribeRole.Definition),
            Node("qualifying", "The target equality supplies the internal root", "qualifying_root",
                new Formula.Logic(SizeEquality, FormulaLogicOperator.Implies, RootInternal),
                "Positive vertex-height supplies an internal vertex and a nonroot child. The last nonroot vertex on the path from that child to the root is a child of the root.",
                DescribeRole.Theorem),
            Node("reduction", "The exact pruning reduction", "pruning_reduction", Reduction(),
                "Depth is unchanged on retained vertices. Every nonroot vertex lies one level below an internal parent, and each internal vertex has a child one level below it. The pruned vertex cardinality is the original internal-vertex count.",
                DescribeRole.Theorem))));

    private static Formula Reduction()
    {
        var successor = Seq(Call("height", Pruned), Plus, D(1));
        var criterion = new Formula.Logic(SizeEquality, FormulaLogicOperator.Iff, Eqn(Call("card", Core), successor));
        return WithRoot(Seq(Eqn(Call("height", T), successor), Sp, Land, Sp, Parenthesized(criterion)));
    }
    private static Formula WithRoot(Formula body) => Seq(Forall, Sp, F.Id("hr"), Colon, Sp,
        RootInternal, Comma, Sp, Parenthesized(body));
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Eqn(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Parameter(string name, Formula type) =>
        Parenthesized(Seq(F.Id(name), Colon, Sp, type));
    private static Formula Finite(Formula carrier) =>
        Seq(OpenBracket, Call("Fintype", carrier), CloseBracket);
    private static Formula For(Formula body, params Formula[] parameters) =>
        Seq(Forall, Sp, Seq(parameters.Select(parameter => Seq(parameter, Sp)).ToArray()), Comma, Sp,
            Parenthesized(body));

    private static Formula Scope(string name, Formula body)
    {
        var v = F.Id("V");
        var carrier = Parameter("V", F.Id("Type"));
        var tree = Parameter("T", Call("Tree", v));
        return name == "prune" ? For(body, carrier, tree) : For(body, carrier, Finite(v), tree);
    }

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("leaf-pruning-" + id),
            DeclarationHandle.Create(Owner + declaration), H(title),
            StatementSource.FromAuthor(Disp(Scope(declaration, formula))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
