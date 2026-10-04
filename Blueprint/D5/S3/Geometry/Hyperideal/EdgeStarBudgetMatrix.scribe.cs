using System;
using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class EdgeStarBudgetMatrixDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The low and high budgets equal weighted transition totals on the actual edge class.", H("Actual edge-star budget matrices"),
        Blocks(Paragraph(Text("Quantify over an arbitrary finite tetrahedron type T, raw involutive face pairing p, color on p.GlobalEdge, valid coloring and e:p.GlobalEdge. In prefix notation, edgeStars(toFacePairedTriangulation(p,color,valid)) is the constructed s, not a free edge star. SameCycle(next(s),i,j) is the cycle relation of that permutation. False denotes face count one, true face count two. beta(4)=arccos(17/33), beta(3)=arccos(49 sqrt(6)/198), beta(2)=arccos(70/99). theta(0)=arccos(31/33), theta(1)=arccos(25/sqrt(726)), theta(2)=arccos(81/88), theta(3)=arccos(61/sqrt(4752)), theta(4)=arccos(23/27). The row/column order false,true gives lowMatrix=[[beta(4),beta(3)],[beta(3),beta(2)]] and highMatrix=[[theta(2),theta(1)],[theta(1),theta(0)]]. Each matrix total is the sum over a,b:Bool of transitionCount(s,e,a,b) times its matrix entry; each budget sums the corresponding high-neighbour weight over occurrences in Fiber(s,e).")),
            Describe.Lean(
                DescribeId.Create("actual-edge-budget-matrix"),
                DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/EdgeStarBudgetMatrix.actual_edge_budget_matrix"),
                H("Cycle classes and both weighted budgets"), StatementSource.FromAuthor(F.Disp(Budget())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each paired slot lies in the same successor cycle, including the case where its face is incoming, using the inverse face map. Conversely successor steps preserve the quotient label. Grouping actual occurrences by their two signatures gives both matrix identities and their exact two-pi equivalences. These are angle-budget identities, not a proof of a common geometric realization."))), DescribeRole.Theorem))));

    private static Formula Budget()
    {
        var T = F.Id("T"); var p = F.Id("p"); var color = F.Id("color");
        var valid = F.Id("valid"); var e = F.Id("e"); var s = Star(p, color, valid);
        var i = F.Id("i"); var j = F.Id("j"); var occurrence = Call("Occurrence", T);
        var twoPi = new Formula.Binary(F.D(2), FormulaBinaryOperator.Multiply, F.Pi);
        var classes = All([("i", occurrence), ("j", occurrence)],
            Iff(Call("SameCycle", Call("next", s), i, j),
                Eq(Call("globalEdge", s, i), Call("globalEdge", s, j))));
        var invariant = All([("i", occurrence)],
            Eq(Call("globalEdge", s, Call("next", s, i)), Call("globalEdge", s, i)));
        var low = Call("lowBudget", s, e); var lowTotal = Call("lowMatrixTotal", s, e);
        var high = Call("highBudget", s, e); var highTotal = Call("highMatrixTotal", s, e);
        return All(Telescope(T, p, color), Imp(Call("Fintype", T), And(classes, invariant,
            Imp(Eq(Call("color", s, e), F.Id("true")),
                And(Eq(low, lowTotal), Iff(Gt(low, twoPi), Gt(lowTotal, twoPi)))),
            Imp(Eq(Call("color", s, e), F.Id("false")),
                And(Eq(high, highTotal), Iff(Gt(high, twoPi), Gt(highTotal, twoPi)))))));
    }

    private static Formula All((string Name, Formula Type)[] vs, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [..vs.Select(v => new Formula.BoundVariable(FormulaIdentifier.Create(v.Name), v.Type))], body);
    private static Formula And(params Formula[] ps)
    {
        var r = ps[^1];
        for (var j = ps.Length - 2; j >= 0; j--) r = new Formula.Logic(ps[j], FormulaLogicOperator.And, r);
        return r;
    }
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Gt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.GreaterThan, b);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(F.Id(name), [..args]);
    private static Formula Star(Formula p, Formula color, Formula valid) =>
        Call("edgeStars", Call("toFacePairedTriangulation", p, color, valid));
    private static (string Name, Formula Type)[] Telescope(Formula T, Formula p, Formula color) =>
        [("T", F.Id("Type")), ("p", Call("RawFacePairing", T)),
         ("color", new Formula.TypeArrow(Call("GlobalEdge", p), F.Id("Bool"))),
         ("valid", Call("ValidColoring", p, color)), ("e", Call("GlobalEdge", p))];
}
