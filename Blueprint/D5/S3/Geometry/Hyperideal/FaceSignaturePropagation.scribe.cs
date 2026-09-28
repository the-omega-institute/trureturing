using System;
using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class FaceSignaturePropagationDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Geometry/Hyperideal/FaceSignaturePropagation.lowPairCount_eq_of_reachable";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Face pairings preserve low opposite-edge counts along balanced dual paths.",
        H("Propagation of balanced face signatures"),
        Blocks(
            Paragraph(Text("Let each local edge of a tetrahedron carry an actual global edge "
                + "label, and color the global labels low or high. Opposite balance means "
                + "the two members of each local opposite-edge pair have the same color. "
                + "The low-pair count reads one edge from each of the three pairs.")),
            Paragraph(Text("A compatible dual adjacency pairs one face of each tetrahedron. "
                + "A permutation of the three face edges identifies their global labels. "
                + "The tetrahedra and the global edge-label set need not be finite.")),
            Describe.Lean(
                DescribeId.Create("balanced-face-signatures-propagate"),
                DeclarationHandle.Create(Declaration),
                H("The low-pair count is constant along balanced dual paths"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For label-preserving face pairings, any two tetrahedra "
                        + "connected by a finite dual path through balanced tetrahedra "
                        + "have the same low-pair count. In particular, a tetrahedron "
                        + "with one low opposite pair cannot be connected to one with "
                        + "two low opposite pairs through balanced tetrahedra alone.")),
                    Paragraph(Text("Each face contains one edge from each opposite pair, "
                        + "so its low-edge count equals the local low-pair count. A face "
                        + "pairing preserves this count because it only permutes three "
                        + "equal-colored global labels. Equality then propagates along "
                        + "the dual path.")),
                    Paragraph(Text("The statement concerns colored edge incidence and "
                        + "face pairings; it assumes no lengths, angles, curvature bounds, "
                        + "or pre-existing geometric realization."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var tType = F.Id("T");
        var eType = F.Id("E");
        var graph = F.Id("G");
        var edge = F.Id("edge");
        var low = F.Id("low");
        var s = F.Id("s");
        var t = F.Id("t");
        var fin6 = Call("Fin", F.D(6));
        var edgeFunction = new Formula.TypeArrow(tType,
            new Formula.TypeArrow(fin6, eType));
        var colorFunction = new Formula.TypeArrow(eType, F.Id("Bool"));
        var glued = Call("faceGluingCompatible", graph, edge);
        var connected = Call("Reachable", Call("balancedGraph", graph, edge, low), s, t);
        var equalCount = Equal(Call("lowPairCount", edge, low, s),
            Call("lowPairCount", edge, low, t));
        return All([
            ("T", F.Id("Type")), ("E", F.Id("Type")),
            ("G", Call("SimpleGraph", tType)),
            ("edge", edgeFunction), ("low", colorFunction),
            ("s", tType), ("t", tType)
        ], Imp(glued, Imp(connected, equalCount)));
    }

    private static Formula All((string Name, Formula Type)[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [.. variables.Select(v => new Formula.BoundVariable(
                FormulaIdentifier.Create(v.Name), v.Type))], body);

    private static Formula Imp(Formula premise, Formula conclusion) =>
        new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
}
