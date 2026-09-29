using System;
using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class CriticalEdgeSignatureWordDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Geometry/Hyperideal/CriticalEdgeSignatureWord.critical_edge_signature_word";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A critical six-occurrence edge star has at most one two-count face signature.",
        H("Critical edge face-signature words"),
        Blocks(
            Paragraph(Text("A raw face pairing defines actual global edges from paired "
                + "face-edge slots. Let s be its oriented edge-star structure after a "
                + "valid low/high coloring. An element i of the fiber over a global "
                + "edge has a local occurrence occ(i) and a six-edge position slot(i). "
                + "The signature of occ(i) records whether its incoming face has "
                + "two low edges.")),
            Describe.Lean(
                DescribeId.Create("critical-six-occurrence-face-signature-word"),
                DeclarationHandle.Create(Declaration),
                H("At most one two-count face"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Suppose a low global edge has six local occurrences. "
                        + "Each has at least three high neighbours, and at least four "
                        + "have four high neighbours. Every occurrence is then either "
                        + "a two-low-edge local pair with four high neighbours or a "
                        + "three-high-neighbour path end. The number of path ends is "
                        + "zero or two.")),
                    Paragraph(Text("No occurrence has both its incoming and successor "
                        + "face signatures equal to two. Around the actual global-edge "
                        + "circle, the resulting binary word forbids adjacent ones and "
                        + "contains at most one one.")),
                    Paragraph(Text("The claim reads face incidence only. It does not "
                        + "identify the opposite edge as another critical global edge, "
                        + "assign shared lengths, or construct a hyperbolic geometry."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var t = F.Id("T");
        var p = F.Id("p");
        var c = F.Id("c");
        var v = F.Id("v");
        var e = F.Id("e");
        var s = Call("edgeStars", Call("toFacePairedTriangulation", p, c, v));
        var i = F.Id("i");
        var occ = Call("occ", i);
        var slot = Call("slot", i);
        var local = Call("localColor", s, occ);
        var high = Call("highNeighbourCount", local, slot);
        var fiber = Call("Fiber", s, e);
        var classified = All([("i", fiber)], Or(
            And(Equal(high, F.D(4)), Equal(Call("colorCard", local, slot), F.D(2))),
            And(Equal(high, F.D(3)), Call("isPathEnd", local, slot))));
        var noTwoTwo = All([("i", fiber)],
            F.Seq(F.Neg, F.Sp, F.Grp(And(
                Equal(Call("signature", s, occ), F.Id("true")),
                Equal(Call("signature", s, Call("next", s, occ)), F.Id("true"))))));
        var conclusion = And(
            classified,
            Or(Equal(Call("pathEndCount", p, c, v, e), F.D(0)),
                Equal(Call("pathEndCount", p, c, v, e), F.D(2))),
            noTwoTwo,
            Le(Call("twoFaceCount", s, e), F.D(1)));
        var premises = And(
            Equal(Call("color", s, e), F.Id("true")),
            All([("i", fiber)], Le(F.D(3), high)),
            Equal(Call("edgeDegree", s, e), F.D(6)),
            Le(F.D(4), Call("fourHighCount", s, e)));
        return All([("T", F.Id("Type")), ("finite", Call("Fintype", t)),
            ("p", Call("RawFacePairing", t)),
            ("c", new Formula.TypeArrow(Call("GlobalEdge", p), F.Id("Bool"))),
            ("v", Call("ValidColoring", p, c)),
            ("e", Call("GlobalEdge", p))], Imp(premises, conclusion));
    }

    private static Formula All((string Name, Formula Type)[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [.. variables.Select(v => new Formula.BoundVariable(
                FormulaIdentifier.Create(v.Name), v.Type))], body);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Or, right);
    private static Formula And(params Formula[] parts)
    {
        if (parts.Length == 0) throw new ArgumentException("Empty conjunction");
        var result = parts[^1];
        for (var j = parts.Length - 2; j >= 0; j--)
            result = new Formula.Logic(parts[j], FormulaLogicOperator.And, result);
        return result;
    }
}
