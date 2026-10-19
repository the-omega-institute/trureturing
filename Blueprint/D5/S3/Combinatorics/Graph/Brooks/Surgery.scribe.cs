using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Brooks;

internal sealed class SurgeryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var v = I("V"); var g = I("G"); var d = I("d"); var k = I("k"); var a = I("A");
        var h = I("H");
        var ih = All("W", C("Type"), Inst("Fintype", I("W"),
            All("H", C("SimpleGraph", I("W")), Inst("DecidableRel", C("Adj", h),
                Imp(Le(C("card", I("W")), k),
                    Imp(C("CliqueFree", h, Add(C("maxDegree", h), D(1))),
                        Imp(Imp(Eq(C("maxDegree", h), D(2)), Not(C("HasOddCycle", h))),
                            C("Colorable", h, C("maxDegree", h)))))))));
        var deleted = C("Induce", g, C("Compl", a));
        var dm = Seq(d, Sp, Minus, Sp, D(1));
        var obstruction = Or(Not(C("CliqueFree", deleted, d)),
            And(Eq(C("maxDegree", deleted), D(2)), C("HasOddCycle", deleted)));
        var premises = And(Eq(d, C("maxDegree", g)), And(Le(D(3), d),
            And(C("CliqueFree", g, Add(d, D(1))),
                And(Not(C("IsContained", C("cliqueMinusEdge", dm), g)),
                    And(C("IsRegularOfDegree", g, d),
                        And(C("Maximal", C("IsIndepSet", g), a),
                            And(Eq(C("maxDegree", deleted), dm),
                                And(Le(C("card", v), Add(k, D(1))),
                                    And(Le(C("card", C("ComplSubtype", a)), k),
                                        And(obstruction, ih))))))))));
        var body = All("d", C("Nat"), All("k", C("Nat"), All("A", C("Set", v),
            Inst("DecidablePred", C("Membership", a),
                Inst("Nonempty", C("ComplSubtype", a), Imp(premises, C("Colorable", g, d)))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Rabern surgery colors a regular graph after deleting a maximal independent set whose induced complement exhibits a clique or an odd cycle.",
            H("Clique and odd-cycle surgery"), Blocks(
                Paragraph(Text("In the formula, card denotes Fintype.card and ComplSubtype(A) is the subtype of vertices outside A. The quantified graph H in the induction hypothesis ranges over the same arbitrary vertex universe as G. Membership(A) denotes the predicate of belonging to A. IsContained is the native adjacency-preserving copy relation.")),
                Describe.Lean(DescribeId.Create("rabern-surgery"),
                    DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Brooks/Surgery.brooksSurgery"),
                    H("The surgery step"), StatementSource.FromAuthor(Disp(Graphs(body))),
                    AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/GraphInvariants/rabern2023brooks")),
                    Blocks(Paragraph(Text("Each vertex in the obstruction has one neighbor in the deleted independent set. Adjacent vertices with different such neighbors determine an edge to add to the smaller graph. Its coloring forces different colors at those two neighbors. A clique then admits a Hall coloring avoiding the prescribed colors. For a longer odd cycle, choose a spanning path, assign the first vertex the last outside-neighbor color, and extend along the path. At the final vertex two neighbors share a color, leaving a free color. A three-cycle uses the clique construction."))),
                    DescribeRole.Theorem))));
    }
    private static Formula C(string n, params Formula[] a) => a.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(n))
        : new Formula.FunctionCall(FormulaIdentifier.Create(n), [.. a]);
    private static Formula I(string n) => F.Id(n);
    private static Formula All(string n, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Inst(string n, Formula a, Formula b) => Seq(OpenBracket, C(n, a), CloseBracket, Sp, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Add(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula Not(Formula a) => new Formula.Not(a);
    private static Formula Graphs(Formula b) => All("V", C("Type"), Inst("Fintype", I("V"),
        All("G", C("SimpleGraph", I("V")), Inst("DecidableRel", C("Adj", I("G")), b))));
}
