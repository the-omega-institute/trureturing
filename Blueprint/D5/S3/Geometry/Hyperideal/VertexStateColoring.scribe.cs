using System;
using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class VertexStateColoringDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Geometry/Hyperideal/VertexStateColoring.balanced_coloring_flat_angle_correspondence";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Balanced binary vertex colorings classify the three opposite-edge flat-angle patterns.",
        H("Binary vertex colors and flat-angle patterns"),
        Blocks(
            Paragraph(Text("Color the four vertices with two symbols, with exactly two vertices "
                + "of each color. Boolean XOR represents addition in the two-element field. "
                + "The three standard colorings are (0,0,1,1), (0,1,0,1), and (0,1,1,0); "
                + "their equal-color edges are respectively the opposite pairs "
                + "12 and 34, 13 and 24, and 14 and 23.")),
            Describe.Lean(
                DescribeId.Create("tetrahedral-binary-vertex-flat-angle-states"),
                DeclarationHandle.Create(Declaration),
                H("Three flat-angle states from balanced vertex colors"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Each standard coloring has two vertices of each color "
                        + "and matches its stated opposite-edge pair. Every balanced coloring "
                        + "matches exactly one of these three edge patterns. Swapping both "
                        + "vertex colors preserves the pattern, so the patterns classify "
                        + "the unlabelled two-two partitions.")),
                    Paragraph(Text("An edge joining equal colors receives flat extension "
                        + "angle pi; an edge joining different colors receives zero. "
                        + "The XOR crossing bit is one exactly on the latter edges, "
                        + "giving the angle as pi times one minus that bit.")),
                    Paragraph(Text("This is a local classification of angle patterns. "
                        + "It supplies neither a positive length realizing a flat block "
                        + "nor a compatible coloring of globally identified vertices."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var k = F.Id("k");
        var b = F.Id("b");
        var i = F.Id("i");
        var j = F.Id("j");
        var fin3 = Call("Fin", F.D(3));
        var fin4 = Call("Fin", F.D(4));
        var colors = new Formula.TypeArrow(fin4, F.Id("Bool"));
        var standard = All([("k", fin3)], And(
            Equal(Call("balanced", Call("stateColor", k)), F.Id("true")),
            Equal(Call("corresponds", Call("stateColor", k), k), F.Id("true"))));
        var matchingStates = Call("filter", Call("finRange", F.D(3)),
            F.Seq(k, F.Sp, F.Mapsto, F.Sp, Call("corresponds", b, k)));
        var classification = All([("b", colors)], Implies(
            Equal(Call("balanced", b), F.Id("true")),
            Equal(Call("length", matchingStates), F.D(1))));
        var crossingBit = Call("toNat", Call("crossing", b, i, j));
        var angle = All([("b", colors), ("i", fin4), ("j", fin4)],
            Equal(Call("flatAngle", b, i, j),
                F.Seq(F.Pi, F.Cdot, F.Sp,
                    F.Grp(F.Seq(F.D(1), F.Minus, crossingBit)))));
        return And(standard, classification, angle);
    }

    private static Formula All((string Name, Formula Type)[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [.. variables.Select(v => new Formula.BoundVariable(
                FormulaIdentifier.Create(v.Name), v.Type))], body);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula And(params Formula[] parts)
    {
        if (parts.Length == 0) throw new ArgumentException("Empty conjunction");
        var result = parts[^1];
        for (var index = parts.Length - 2; index >= 0; index--)
            result = new Formula.Logic(parts[index], FormulaLogicOperator.And, result);
        return result;
    }
}
