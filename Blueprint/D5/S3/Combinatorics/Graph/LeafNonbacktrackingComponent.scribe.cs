using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class LeafNonbacktrackingComponentDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/LeafNonbacktrackingComponent.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An actual nonempty walk between leaves in a finite graph of degree at most two, with no immediate backtracking, is the entire simple path component.",
        H("Nonbacktracking Leaf Walks Exhaust Their Components"),
        Blocks(
            Paragraph(Text(
                "Let G be a simple graph on a finite type V with decidable equality. Assume every "
                + "neighbor set has at most two elements. Nonbacktracking(p) means that the actual "
                + "vertices at positions i and i+2 differ whenever i+2 is within p's length. "
                + "Nil(p) means that p has no edges. "
                + "Sym2Mk(x,y) denotes the unordered pair s(x,y) used for graph edges. "
                + "A leaf condition is expressed as a subsingleton neighbor set. It does not "
                + "assume a chosen path, an endpoint matching or any component coverage.")),
            Describe.Lean(DescribeId.Create("leaf-simple-path"),
                DeclarationHandle.Create(Prefix + "nonbacktracking_leaf_isPath"),
                H("A Nonbacktracking Walk from a Leaf Is Simple"),
                StatementSource.FromAuthor(PathFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every actual walk starting at a leaf and having no immediate backtracking "
                    + "is a path. Strong induction on its actual length examines the prefix before "
                    + "the last edge. At each internal prefix vertex the two path neighbors exhaust "
                    + "the ambient neighbor set; at the starting leaf its one path neighbor does "
                    + "so. Returning to an earlier vertex would therefore use the prefix's last "
                    + "edge backwards, contradicting the actual nonbacktracking condition."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("leaf-full-component"),
                DeclarationHandle.Create(Prefix + "nonbacktracking_leaf_full_component"),
                H("A Nonempty Leaf-to-Leaf Walk Is the Whole Component"),
                StatementSource.FromAuthor(ComponentFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If the actual walk is nonempty and its endpoint also has a subsingleton "
                    + "neighbor set, its endpoints are distinct and each has exactly one neighbor. "
                    + "Its actual support consists exactly of the vertices reachable from its "
                    + "start. An ambient edge occurs in the actual walk exactly when its first "
                    + "endpoint is in that component. Other disconnected components are excluded. "
                    + "The first theorem earns the path condition. The endpoint leaf condition "
                    + "then saturates the final neighbor set as well, so no edge leaves the support. "
                    + "Induction along any actual reachable walk proves full component coverage."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "For the prefix-reversal construction, this bridge turns a proved legal native "
                + "word with different consecutive involutive generators and actual leaf endpoints "
                + "into a complete path component after the cuts. One must still earn its degree "
                + "bound, its leaf conditions and every legal native edge. Those native facts and "
                + "the six-cut pairing are separate proof obligations.")))));

    private static Formula PathFormula() => Quantify(
        Implies(BasicHypotheses(), Call("IsPath", F.Id("p"))));

    private static Formula ComponentFormula()
    {
        Formula p = F.Id("p"), a = F.Id("a"), b = F.Id("b");
        Formula x = F.Id("x"), y = F.Id("y"), v = F.Id("V");
        Formula support = All("x", v, Iff(Member(x, Call("support", p)), Call("Reachable", F.Id("G"), a, x)));
        Formula edges = All("x", v, All("y", v,
            Iff(And(Call("Adj", F.Id("G"), x, y), Call("Reachable", F.Id("G"), a, x)),
                Member(Call("Sym2Mk", x, y), Call("edges", p)))));
        Formula result = And(Call("IsPath", p), And(new Formula.Relation(a, FormulaRelationOperator.NotEqual, b),
            And(Equal(Call("ncard", Call("neighborSet", F.Id("G"), a)), D(1)),
                And(Equal(Call("ncard", Call("neighborSet", F.Id("G"), b)), D(1)), And(support, edges)))));
        return Quantify(Implies(And(BasicHypotheses(),
            And(Call("Subsingleton", Call("neighborSet", F.Id("G"), b)),
                new Formula.Not(Seq(Open, Call("Nil", p), Close)))), result));
    }

    private static Formula BasicHypotheses() => And(
        All("z", F.Id("V"), new Formula.Relation(
            Call("ncard", Call("neighborSet", F.Id("G"), F.Id("z"))), FormulaRelationOperator.LessThanOrEqual, D(2))),
        And(Call("Subsingleton", Call("neighborSet", F.Id("G"), F.Id("a"))), Call("Nonbacktracking", F.Id("p"))));

    private static Formula Quantify(Formula body) => Disp(All("V", Call("Type"),
        Seq(OpenBracket, Call("DecidableEq", F.Id("V")), CloseBracket, Sp,
            OpenBracket, Call("Finite", F.Id("V")), CloseBracket, Sp,
            All("G", Call("SimpleGraph", F.Id("V")), All("a", F.Id("V"), All("b", F.Id("V"),
                All("p", Call("Walk", F.Id("G"), F.Id("a"), F.Id("b")), body)))))));
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
            : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Member(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula Iff(Formula left, Formula right) => Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula And(Formula left, Formula right) => Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) => Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Logic(Formula left, FormulaLogicOperator op, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), op, Seq(Open, right, Close));
}
