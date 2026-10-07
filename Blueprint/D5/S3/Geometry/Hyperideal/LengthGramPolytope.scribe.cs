using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class LengthGramPolytopeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The common six-length cut simplex is exactly the convex hull of twelve labeled endpoints.",
        H("The finite vertices of the same common body"),
        Blocks(
            Paragraph(Text("Let l be six strictly positive lengths in the order "
                + "(01,02,03,23,13,12), with all six coordinates free to vary. "
                + "Write G for the symmetric matrix with diagonal one and off-diagonal "
                + "minus cosh of the corresponding length. C is the same nonnegative "
                + "unit-sum simplex cut by Gv<=0. For different labels i,j, define "
                + "p(i,j)=(-Gij*ei+ej)/(1-Gij), with ei the standard coordinate vector. "
                + "L is the set of ordered pairs of distinct labels in Fin 4; "
                + "P sends a label (i,j) to p(i,j), and V is its range. "
                + "R6 and R4 denote the real six- and four-coordinate spaces. "
                + "row(l,r,v) denotes the r-th row of G times v.")),
            Describe.Lean(
                DescribeId.Create("six-length-cut-body-polytope"),
                DeclarationHandle.Create(
                    "D5/S3/Geometry/Hyperideal/LengthGramPolytope.cut_body_polytope"),
                H("No additional extreme points"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("A tight truncation inequality forces its "
                        + "coordinate to exceed one half, so two truncations cannot "
                        + "be tight together. A feasible point has at least two positive "
                        + "coordinates. With no tight truncation, transfer a small "
                        + "amount of mass between two positive coordinates in both "
                        + "directions. With one tight truncation and at least three "
                        + "positive coordinates, a nonzero three-coordinate direction "
                        + "preserves both the coordinate sum and that tight row. "
                        + "Continuity preserves all remaining strict inequalities "
                        + "for a sufficiently small perturbation in either direction. "
                        + "Each case gives a nontrivial open segment through the point, "
                        + "excluding extremality.")),
                    Paragraph(Text("Thus an extreme point has precisely two positive "
                        + "coordinates and one tight truncation. These two equalities "
                        + "determine p(i,j). Conversely, any strict convex combination "
                        + "equal to p(i,j) forces its two terms to have the same support "
                        + "and tight row, and therefore to equal p(i,j). "
                        + "The compact convex body is the closed convex hull of its "
                        + "extreme points by Krein-Milman. The hull of the finite "
                        + "endpoint set is closed, giving the stated exact hull.")),
                    Paragraph(Text("The support recovers the original edge, while "
                        + "the unique tight row recovers its ordered endpoint. "
                        + "Hence the twelve labels produce twelve distinct points. "
                        + "This classifies the coefficient body used by the common "
                        + "radial normalization and actual Lorentz frame. Identification "
                        + "with the eight geometric halfspaces, interior, complete "
                        + "hyperbolic face and edge incidence, prescribed distances, "
                        + "angles, rigidity, volume and gluing remain separate geometric "
                        + "claims. Zero-length degenerations are outside the strict "
                        + "positive-length domain of this statement."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var l = F.Id("l");
        var i = F.Id("i");
        var j = F.Id("j");
        var k = F.Id("k");
        var r = F.Id("r");
        var c = Call("C", l);
        var v = Call("V", l);
        var p = Call("p", l, i, j);
        return All("l", F.Id("R6"), Implies(
            All("k", Call("Fin", F.D(6)), Lt(F.D(0), Call("coord", l, k))),
            And(Eq(Call("extremePoints", F.Id("Real"), c), v),
                Eq(Call("convexHull", F.Id("Real"), v), c),
                Call("Injective", Call("P", l)),
                All("i", Call("Fin", F.D(4)), All("j", Call("Fin", F.D(4)),
                    Implies(Call("distinct", i, j), And(
                        In(p, c), Lt(F.D(0), Call("coord", p, i)),
                        Lt(F.D(0), Call("coord", p, j)),
                        All("k", Call("Fin", F.D(4)), Implies(
                            And(Call("distinct", k, i), Call("distinct", k, j)),
                            Eq(Call("coord", p, k), F.D(0)))),
                        Eq(Call("row", l, i, p), F.D(0)),
                        All("r", Call("Fin", F.D(4)), Implies(Call("distinct", r, i),
                            Lt(Call("row", l, r, p), F.D(0)))))))))));
    }

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create(name), domain, body);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
    private static Formula And(params Formula[] clauses)
    {
        var result = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(clauses[i], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula In(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
}
