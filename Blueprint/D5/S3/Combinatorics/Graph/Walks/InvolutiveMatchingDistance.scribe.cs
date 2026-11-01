using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class InvolutiveMatchingDistanceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite extension walks reduce to base walks with at most one matching step.", H("Exact distances after an involutive matching extension"), Blocks(
            Paragraph(Text("Let G be any simple graph and e a graph automorphism satisfying e(e(u))=u. The extension is the union of G with the undirected loop-free relation joining u to e(u). No finiteness is needed for the walk normal form. For the distance formula G is connected.")),
            Node("walk_normal_form", "A native walk normal form",
                All("p",C("Walk",C("extension",I("e")),I("u"),I("v")),Or(Ex("q",C("Walk",I("G"),I("u"),I("v")),Le(C("length",I("q")),C("length",I("p")))),Ex("q",C("Walk",I("G"),C("apply",I("e"),I("u")),I("v")),Le(C("add",C("length",I("q")),D(1)),C("length",I("p")))))),
                "Induct on the actual extension walk. A base edge is transported through e when necessary. A matching edge toggles the normal form, and two matching steps cancel by involutivity. The resulting base walk never uses more edges than the original walk, counting the possible matching step."),
            Node("distance", "The exact minimum formula",
                All("u",I("V"),All("v",I("V"),Eq(C("dist",C("extension",I("e")),I("u"),I("v")),C("min",C("dist",I("G"),I("u"),I("v")),C("add",D(1),C("dist",I("G"),C("apply",I("e"),I("u")),I("v"))))))),
                "Base geodesics give both upper bounds, inserting one matching edge for the second bound. Apply the normal form to an extension geodesic to obtain the reverse bound. Fixed points of e cause no difficulty because their extra matching step cannot improve the base distance.")), []));
    private static DocumentBlock Node(string name, string title, Formula statement, string explanation) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/InvolutiveMatchingDistance." + name), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))),
            name is "mobiusIso" or "pentagon_square_complement_iso" ? DescribeRole.Definition : DescribeRole.Theorem);
    private static Formula I(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] a) => a.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(s))
        : new Formula.FunctionCall(FormulaIdentifier.Create(s), [.. a]);
    private static Formula All(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Ex(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), t, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
}
