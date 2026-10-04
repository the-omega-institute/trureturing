using System;
using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class CriticalEdgeSignatureWordDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A critical six-occurrence low edge has no adjacent two-count signatures and at most one such face.", H("Critical six-occurrence signature words"),
        Blocks(Paragraph(Text("Use the raw face pairing and valid coloring on arbitrary finite T. Prefix notation for the constructed edge star is as in the budget statement. Fiber(s,e) contains occurrences, not distinct neighbour labels; val(i) is its underlying occurrence and snd(val(i)) its local edge. edgeDegree is the fiber cardinality, fourHighCount counts occurrences with four high neighbours, and twoFaceCount counts true signatures. The low edge has six occurrences, every occurrence has at least three high neighbours and at least four have four high neighbours. No equality of global opposite labels, manifold-link certification, continuous angle margin or geometric closure is asserted.")),
            Describe.Lean(
                DescribeId.Create("critical-edge-signature-word"),
                DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/CriticalEdgeSignatureWord.critical_edge_signature_word"),
                H("Classification, endpoint parity and the cyclic word"), StatementSource.FromAuthor(F.Disp(Word())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Finite local classification permits only the four-high/color-cardinality-two case or the three-high/path-end case. At least four four-high occurrences leave at most two path ends. Actual edge balance forces their number to be zero or two. No occurrence has a true-to-true transition; counting false-to-true transitions then bounds the number of true signatures by one."))), DescribeRole.Theorem))));

    private static Formula Word()
    {
        var T = F.Id("T"); var p = F.Id("p"); var color = F.Id("color");
        var valid = F.Id("valid"); var e = F.Id("e"); var s = Star(p, color, valid);
        var i = F.Id("i"); var z = Call("val", i); var local = Call("localColor", s, z);
        var target = Call("snd", z); var neighbours = Call("highNeighbourCount", local, target);
        var fiber = Call("Fiber", s, e); var ends = Call("pathEndCount", p, color, valid, e);
        var atLeastThree = All([("i", fiber)], Le(F.D(3), neighbours));
        var classification = All([("i", fiber)], Or(
            And(Eq(neighbours, F.D(4)), Eq(Call("colorCard", local, target), F.D(2))),
            And(Eq(neighbours, F.D(3)), Call("isPathEnd", local, target))));
        var noAdjacent = All([("i", fiber)], new Formula.Not(And(
            Eq(Call("signature", s, z), F.Id("true")),
            Eq(Call("signature", s, Call("next", s, z)), F.Id("true")))));
        var result = And(classification, Or(Eq(ends, F.D(0)), Eq(ends, F.D(2))),
            noAdjacent, Le(Call("twoFaceCount", s, e), F.D(1)));
        return All(Telescope(T, p, color), Imp(Call("Fintype", T),
            Imp(Eq(new Formula.Apply(color, [e]), F.Id("true")),
                Imp(atLeastThree, Imp(Eq(Call("edgeDegree", s, e), F.D(6)),
                    Imp(Le(F.D(4), Call("fourHighCount", s, e)), result))))));
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
