using System;
using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class TwoLengthAngleSumDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Geometry/Hyperideal/TwoLengthAngleSum.two_length_angle_sum";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The selected edges of a two-length generalized tetrahedron have a strict total-angle lower bound on the full unbounded parameter domain.",
        H("Two lengths and the sum over actual selected edge positions"),
        Blocks(
            Paragraph(Text("A and B are cosine-length coordinates, with A>1 and B>4A+5. The six local positions have the original order (12,13,14,34,24,23). S is any subset of these six positions with at least two elements; position j reads B exactly when j is in S and otherwise reads A. Cardinality counts positions, so repeated global labels do not collapse local occurrences.")),
            Paragraph(Text("For a six-vector x and target position q, use the existing FourCycleCurvature.frame to read the target, four neighbors and opposite coordinate in the original FourCycleEnvelopes.cosine. Thus the raw cosine is the original numerator divided by the two positive square roots. extendedAngle(x,q) is arccos(max(-1,min(rawCos(x,q),1))). AngleSum(A,B,S) abbreviates the sum of these extended angles over every q in S, with x(j)=B for j in S and A otherwise. card(S) denotes its finite cardinality.")),
            Describe.Lean(
                DescribeId.Create("two-length-continuous-angle-sum"),
                DeclarationHandle.Create(Declaration),
                H("The complete selected-edge sum exceeds one quarter pi per occurrence"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The proof establishes the missing continuous cosine bounds from the actual numerator and radicands. Write a=A-1 and b=B-4A-5, so both are positive and B=9+4a+b. For each useful edge, the negative-numerator alternative or squared-denominator gap is exactly a polynomial with positive coefficients and a positive constant term. These certificates prove the inequalities for every real parameter in the stated unbounded region; no desired cosine or angle bound is assumed.")),
                    Paragraph(Text("There are 57 selected-edge subsets of size at least two, grouped into nine K4 graph types. Adjacent pairs, triangles and four-cycles use every selected angle above pi/3. Opposite pairs use two angles above pi/2; stars and the all-six type use every selected angle above pi/4. A three-edge path uses its two endpoints above pi/2. The four-edge graph complementary to an adjacent pair uses its selected opposite pair above pi/2. A five-edge graph uses the four edges adjacent to the missing edge above pi/3. The finite slot routing checks every actual subset directly. Adding the other nonnegative extended angles gives the complete sum with all its multiplicities.")),
                    Paragraph(Text("For A=2, B=14 and the path S={0,3,5}, the middle position 5 has raw numerator 2466, both radicands 1179, and raw cosine 274/131>1. Its extended angle is zero, while the total selected-edge estimate remains strict. The result therefore includes generalized states with zero angles and does not require the tetrahedron to be genuinely nondegenerate.")),
                    Paragraph(Text("This is an estimate for the specified original six-slot cosine and its clipped extension. Its use with actual geometric dihedral angles requires their identification with this formula and one common global length vector. The theorem supplies neither volume-maximizer existence, global face gluing, normal-link topology nor same-manifold geometric realization, and it does not settle unrestricted CFMP. The original cosine formula and generic square-root, inverse-cosine and finite-sum facts are reused; no literature priority is asserted."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var A = F.Id("A"); var B = F.Id("B"); var S = F.Id("S");
        var count = Call("card", S);
        var premises = And(Lt(F.D(1), A),
            Lt(Call("add", Call("mul", F.D(4), A), F.D(5)), B),
            Le(F.D(2), count));
        var bound = Call("div", Call("mul", count, F.Id("pi")), F.D(4));
        return All([("A", F.Id("Real")), ("B", F.Id("Real")),
            ("S", Call("Finset", Call("Fin", F.D(6))))],
            Imp(premises, Lt(bound, Call("AngleSum", A, B, S))));
    }

    private static Formula All((string Name, Formula Type)[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [..variables.Select(v => new Formula.BoundVariable(FormulaIdentifier.Create(v.Name), v.Type))], body);
    private static Formula And(params Formula[] clauses)
    {
        if (clauses.Length == 0) throw new ArgumentException("Empty conjunction");
        var result = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(clauses[i], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(F.Id(name), [..args]);
}
