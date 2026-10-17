using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeJ2SurvivingEdgesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2SurvivingEdges.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Each independently specified native J2 word constructs an actual simple path exhausting its full component after the six actual marked F2 edges are removed.",
        H("Five Actual Surviving J2 Path Components"),
        Blocks(
            Describe.Lean(DescribeId.Create("native-j2-word-full-component"),
                DeclarationHandle.Create(Prefix + "native_j2_word_full_component"),
                H("Every Literal Word Exhausts Its Actual Component"),
                StatementSource.FromAuthor(ComponentFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every m at least five and i in Fin(5), there is an actual walk in "
                        + "survivingGraph(m) from the independently specified wordStart(m,i) to "
                        + "wordFinish(m,i). It is simple, has exactly wordLength(m,i) edges, and "
                        + "its complete support is the literal left multiplication scan of word(m,i). "
                        + "A configuration lies in its support exactly when it is reachable from "
                        + "its start in the actual surviving graph. Moreover, an arbitrary actual "
                        + "surviving edge incident to that component occurs in this same walk, and "
                        + "every edge of this walk is such an edge.")),
                    Paragraph(Text(
                        "The surviving graph is specified before choosing the words or a walk: "
                        + "take the complete actual F2 native edges outside all T/E cuts together "
                        + "with every actual T/E c seam, then remove exactly the six independently "
                        + "specified marked b edges. Literal c-step coordinates identify the exact "
                        + "T or E seam owner. Full lower and contact native-circle complements earn "
                        + "each repeated H row. The short reflected and positive rows separately "
                        + "avoid the actual selected cuts and terminal-marked b edges, including "
                        + "both F2 b cuts in the contact circle. Exact seed products and repeated-block "
                        + "products then concatenate these earned rows into all five complete words.")),
                    Paragraph(Text(
                        "The same actual F2 Hamilton witness bounds the surviving degree by two "
                        + "and makes each independently specified port a graph leaf after its marked "
                        + "edge is removed. Consecutive literal generators never multiply to the "
                        + "identity. Cancellation turns this letter law into nonbacktracking of the "
                        + "actual constructed walk. The earned leaf/nonbacktracking component theorem "
                        + "then proves simplicity, complete vertex reachability and the complete "
                        + "incident-edge inventory. No path, component coverage, endpoint matching, "
                        + "or step-legality hypothesis is supplied by the caller."))), DescribeRole.Theorem),
            Paragraph(Text(
                "This result constructs the five stated components. Identifying the sixth "
                + "component and establishing the higher actual recursive expansion and "
                + "Hamilton cycles for all sizes are further mathematical obligations.")))));

    private static Formula ComponentFormula()
    {
        Formula m = F.Id("m"), i = F.Id("i"), w = F.Id("w"), x = F.Id("x"), y = F.Id("y");
        Formula graph = Call("survivingGraph", m), start = Call("wordStart", m, i);
        Formula reach(Formula v) => Call("Reachable", graph, start, v);
        Formula vertices = All("x", Call("Configuration", m),
            Iff(Call("Member", x, Call("Support", w)), reach(x)));
        Formula edges = All("x", Call("Configuration", m), All("y", Call("Configuration", m),
            Iff(And(Call("Adj", graph, x, y), reach(x)),
                Call("Member", Call("Sym2Pair", x, y), Call("Edges", w)))));
        Formula body = Some("w", Call("Walk", graph, start, Call("wordFinish", m, i)),
            And(Call("IsPath", w), And(Eq(Call("Length", w), Call("wordLength", m, i)),
                And(Eq(Call("Support", w), Call("ScanlMul", start, Call("word", m, i))),
                    And(vertices, edges)))));
        return Disp(All("m", Call("Nat"), Implies(Le(D(5), m), All("i", Call("Fin", D(5)), body))));
    }

    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Some(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
}
