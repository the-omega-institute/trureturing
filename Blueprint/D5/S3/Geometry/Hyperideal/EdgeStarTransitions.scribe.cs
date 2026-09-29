using System;
using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class EdgeStarTransitionsDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Geometry/Hyperideal/EdgeStarTransitions.global_edge_balance";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Directed face-signature transitions balance on every global edge.",
        H("Face signatures around global edges"),
        Blocks(
            Paragraph(Text("Number each tetrahedron's edges (12,13,14,34,24,23). "
                + "Pairing corresponding edge slots across faces generates the equivalence "
                + "classes of actual global edges. Every tetrahedron contributes six distinct "
                + "local edge occurrences, even when several belong to the same global edge. "
                + "A color is assigned to each global edge, and every face has one or two "
                + "low edges.")),
            Paragraph(Text("A fixed-point-free involution pairs whole faces, and the "
                + "three edge slots on each face are transported by an inverse pair "
                + "of permutations. This pairing admits a compatible orientation "
                + "of every normal edge link. Each outgoing face is mapped to the next "
                + "incoming face. "
                + "Its single three-edge permutation sends the outgoing local edge slot "
                + "to the next local edge occurrence. The resulting successor permutes "
                + "all occurrences along oriented normal edge links and preserves "
                + "their global-edge classes.")),
            Paragraph(Text("The Boolean signature records a face count of one as false and "
                + "two as true. A rise is a one-to-two transition; a fall is a two-to-one "
                + "transition. A path end is a local edge at an end of the three-edge path "
                + "formed by edges of its own color.")),
            Describe.Lean(
                DescribeId.Create("normal-edge-circle-transition-balance"),
                DeclarationHandle.Create(Declaration),
                H("Rises equal falls and path ends have even multiplicity"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For each actual global edge of a finite face-paired tetrahedron "
                        + "system, the number of one-to-two transitions equals the number "
                        + "of two-to-one transitions. Local path-end edge occurrences on "
                        + "that same global edge have even multiplicity.")),
                    Paragraph(Text("A six-edge incidence check identifies a local path end "
                        + "exactly when its two adjacent face signatures differ. Gluing "
                        + "preserves all three labels on a paired face, so each outgoing "
                        + "signature equals the next incoming one. Reindexing by the "
                        + "label-preserving successor makes the transition counts equal; "
                        + "their sum is therefore even.")),
                    Paragraph(Text("The conclusion concerns colored face incidence on the "
                        + "normal circle and uses no edge lengths or angle estimates."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var t = F.Id("T");
        var pairing = F.Id("p");
        var color = F.Id("c");
        var valid = F.Id("v");
        var globalEdge = F.Id("e");
        return All([
            ("T", F.Id("Type")),
            ("finite", Call("Fintype", t)),
            ("p", Call("RawFacePairing", t)),
            ("c", new Formula.TypeArrow(Call("GlobalEdge", pairing), F.Id("Bool"))),
            ("v", Call("ValidColoring", pairing, color)),
            ("e", Call("GlobalEdge", pairing))
        ], And(Equal(Call("rise", pairing, color, valid, globalEdge),
            Call("fall", pairing, color, valid, globalEdge)),
            Call("Even", Call("pathEndCount", pairing, color, valid, globalEdge))));
    }

    private static Formula All((string Name, Formula Type)[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [.. variables.Select(v => new Formula.BoundVariable(
                FormulaIdentifier.Create(v.Name), v.Type))], body);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
}
