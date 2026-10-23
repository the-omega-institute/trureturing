using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeJ2SurvivingModelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2SurvivingModel.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual surviving graph uses the complete F2 edge inventory with exactly the six independently specified marked edges removed.",
        H("The Actual F2 Six-Cut Graph"),
        Blocks(
            Definition("MarkedCut", "The Six Independently Specified Cuts", MarkedFormula(),
                "MarkedCut(m,e) means e equals markedEdge(m,q) for q in Fin(3) times Bool. "
                + "These six actual b edges have disjoint endpoint sets because all twelve "
                + "independently specified ports are distinct."),
            Definition("SurvivingEdge", "The Independent Surviving Edge Inventory", SurvivingFormula(),
                "An undirected edge survives exactly when it is an actual F2 native edge "
                + "outside F2DeletedEdge or an actual F2 c seam, and it is outside MarkedCut. "
                + "No word, walk support or chosen component defines this predicate."),
            Definition("survivingGraph", "The Graph Built from the Surviving Inventory", GraphFormula(),
                "survivingGraph(m) is SimpleGraph.fromEdgeSet applied to the set of edges "
                + "satisfying SurvivingEdge(m). Its adjacency law is the surviving inventory "
                + "at s(x,y), together with x distinct from y."),
            Paragraph(Text(
                "The internal proof takes one actual F2 Hamilton witness containing all "
                + "six marked edges. Mapping the original actual cycle into "
                + "the Cayley graph bounds surviving degree by two. Each port loses its "
                + "marked incident edge, so its surviving neighbor set has at most one "
                + "element. These earned facts are consumed by the actual word-component proof.")))));

    private static DocumentBlock Definition(string selector, string title, Formula formula, string meaning) =>
        Describe.Lean(DescribeId.Create(selector.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + selector), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(meaning))), DescribeRole.Definition);

    private static Formula MarkedFormula()
    {
        Formula m = F.Id("m"), e = F.Id("e"), q = F.Id("q");
        return Disp(All("m", Call("Nat"), All("e", Call("Sym2", Call("Configuration", m)),
            Iff(Call("MarkedCut", m, e), Some("q", Call("Prod", Call("Fin", D(3)), Call("Bool")),
                Eq(e, Call("markedEdge", m, q)))))));
    }

    private static Formula SurvivingFormula()
    {
        Formula m = F.Id("m"), e = F.Id("e");
        return Disp(All("m", Call("Nat"), All("e", Call("Sym2", Call("Configuration", m)),
            Iff(Call("SurvivingEdge", m, e),
                And(Or(And(Call("F2NativeEdge", m, e), Neg(Call("F2DeletedEdge", m, e))),
                    Call("F2Seam", m, e)), Neg(Call("MarkedCut", m, e)))))));
    }

    private static Formula GraphFormula()
    {
        Formula m = F.Id("m"), x = F.Id("x"), y = F.Id("y");
        return Disp(All("m", Call("Nat"), All("x", Call("Configuration", m),
            All("y", Call("Configuration", m), Iff(Call("Adj", Call("survivingGraph", m), x, y),
                And(Call("SurvivingEdge", m, Call("Sym2Pair", x, y)), Neg(Eq(x, y))))))));
    }

    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Some(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Neg(Formula a) => new Formula.Not(a);
}
