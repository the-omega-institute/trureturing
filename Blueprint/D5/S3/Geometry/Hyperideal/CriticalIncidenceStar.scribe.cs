using System;
using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class CriticalIncidenceStarDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Geometry/Hyperideal/CriticalIncidenceStar.critical_incidence_face_bounds";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Separate exact curvature margins for a six-occurrence global critical edge star.",
        H("Critical edge incidence margins"),
        Blocks(
            Paragraph(Text("A finite tetrahedron type T and a global edge-label type E carry "
                + "an incidence map from each of six local edge slots to E. The star of e is "
                + "the fibre of that map; StarOccurrence(s,e) is its subtype of local "
                + "occurrences. Its cardinality counts local occurrences, including "
                + "repeated tetrahedra and repeated neighbouring global labels. The local "
                + "frame puts each target slot first and its opposite fourth.")),
            Paragraph(Text("Critical labels are low labels of degree six. Every occurrence "
                + "of the target has at least three high neighbours. A chosen subset of at "
                + "least four occurrences has four high neighbours and a critical opposite "
                + "label. The global length function assigns one value to each global edge. "
                + "All values lie in [1,2], high values are at most 5/4, and critical values "
                + "are at least 4/3. The same box applies to both target faces.")),
            Describe.Lean(
                DescribeId.Create("critical-incidence-exact-face-bounds"),
                DeclarationHandle.Create(Declaration),
                H("Each face has its own curvature margin"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("At target length 4/3, each local cosine is at least "
                        + "4/7; six angle terms give curvature at least "
                        + "2pi-6arccos(4/7). At target length 2, every angle is at least "
                        + "beta=arccos(49/sqrt(6534)); each favourable angle is at least "
                        + "gamma=arccos(43/99). Four favourable occurrences give curvature "
                        + "at most the negative of 4gamma+2beta-2pi.")),
                    Paragraph(Text("Both inequalities hold for any one global length vector "
                        + "satisfying the box and the stated target-face equality. Local "
                        + "occurrences with the same global neighbour read the same length. "
                        + "The result concerns the analytic angle formula on labelled edge "
                        + "incidence; it does not assert face-gluing manifold conditions or "
                        + "geometric realization."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var t = F.Id("T"); var eType = F.Id("E"); var s = F.Id("s");
        var edge = F.Id("e"); var x = F.Id("x"); var good = F.Id("good");
        var critical = F.Id("critical"); var a = F.Id("a"); var f = F.Id("f");
        var occurrence = Call("StarOccurrence", s, edge);
        var criticalClass = All([("f", eType)], Imp(Call("critical", f),
            And(Eq(Call("low", s, f), F.Id("true")),
                Eq(Call("degree", s, f), F.D(6)))));
        var threeHigh = All([("a", occurrence)], Call("ThreeHigh", s, a));
        var favourable = All([("a", occurrence)], Imp(Member(a, good),
            And(Call("FourHigh", s, a),
                Call("critical", Call("coordinate", s, a, F.D(3))))));
        var box = All([("f", eType)], And(
            Member(Call("x", f), Call("Icc", F.D(1), F.D(2))),
            Imp(Eq(Call("low", s, f), F.Id("false")),
                Le(Call("x", f), Rat(5, 4))),
            Imp(Call("critical", f), Le(Rat(4, 3), Call("x", f)))));
        var premises = And(Call("Fintype", t), Call("DecidableEq", eType),
            Call("critical", edge),
            Le(F.D(4), Call("card", good)), criticalClass,
            threeHigh, favourable, box);
        var pi = F.Id("pi");
        var lower = F.Seq(F.D(2), F.Cdot, F.Sp, pi, F.Minus,
            F.D(6), F.Cdot, F.Sp, Call("arccos", Rat(4, 7)));
        var upper = F.Seq(F.D(4), F.Cdot, F.Sp, F.Id("gamma"), F.Plus,
            F.D(2), F.Cdot, F.Sp, F.Id("beta"), F.Minus,
            F.D(2), F.Cdot, F.Sp, pi);
        var result = And(
            Imp(Eq(Call("x", edge), Rat(4, 3)),
                Le(lower, Call("curvature", s, x, edge))),
            Imp(Eq(Call("x", edge), F.D(2)),
                Le(Call("curvature", s, x, edge),
                    F.Seq(F.Minus, F.Grp(upper)))));
        return All([("T", F.Id("Type")), ("E", F.Id("Type")),
            ("s", Call("Incidence", t, eType)),
            ("critical", new Formula.TypeArrow(eType, F.Id("Prop"))),
            ("e", eType), ("good", Call("Finset", occurrence)),
            ("x", new Formula.TypeArrow(eType, F.Id("Real")))],
            Imp(premises, result));
    }

    private static Formula All((string Name, Formula Type)[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [.. variables.Select(v => new Formula.BoundVariable(
                FormulaIdentifier.Create(v.Name), v.Type))], body);

    private static Formula And(params Formula[] parts)
    {
        if (parts.Length == 0) throw new ArgumentException("Empty conjunction");
        var result = parts[^1];
        for (var i = parts.Length - 2; i >= 0; i--)
            result = new Formula.Logic(parts[i], FormulaLogicOperator.And, result);
        return result;
    }

    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Member(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula Rat(int numerator, int denominator) =>
        F.Seq(F.Frac, F.Grp(F.D((byte)numerator)), F.Grp(F.D((byte)denominator)));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
}
