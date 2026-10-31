using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Jacobi;

internal sealed class FlagPruningDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Jacobi/FlagPruning.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual leaf pruning extracts singly attached ordinary hair trees", H("Actual leaf pruning extracts singly attached ordinary hair trees"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-leaf-pruning"),
                DeclarationHandle.Create(Prefix + "LeafPruning"), H("Chronological deletion with literal residual flag degree"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A LeafPruning of a finite cyclic FlagGraph assigns distinct chronological ranks to removed rotor orbits and the terminal rank to retained orbits. Each removal has at most one literal flag whose mate still belongs to a vertex of the same or a later rank; both flags of any loop are therefore counted. All numbered anchor vertices are protected, and every terminal nonanchor vertex has at least two remaining flags. The source incidence graph retains actual rotor orbits and individual edge flags separately, preserving loops and parallel edges. Source stability means an actual incidence cycle or two distinct protected anchor vertices. No forest, boundary, binary-tree shape or placement property is part of the pruning input."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-pruned-component-extraction"),
                DeclarationHandle.Create(Prefix + "extractComponentHair"), H("Extracting the literal open tree and its external parent"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a connected stable source, deletion ranks refine to leaf-deletion ranks on the actual incidence graph. The earliest vertex of a cycle or of a simple path with retained endpoints cannot be deleted. Consequently the retained incidence core is connected and contains an edge. Every deleted component is acyclic and has exactly one boundary adjacency: a path between two boundaries would force its earliest vertex to have two distinct later neighbors. The expanded deleted component contains one exterior mate flag at its retained parent; removing this degree-one flag leaves precisely the incidence graph of the extracted OpenHair. Its flag set consists exactly of original flags whose removed owner vertex lies in the component. Rotor and labels are inherited literally, and only the root pairing is changed to a fixed point. The connected core supplies another retained flag at the exterior owner, proving that the disjoint ambient parent is trivalent. Anchor protection makes every univalent component flag ordinary. The resulting PrunedComponentHair records the tree proof, actual OpenHairPlacement, exact source flag range, unique boundary and equality with the original rotor-fixed component leaf count."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("pruned-branching-component-vanishing"),
                DeclarationHandle.Create(Prefix + "pruned_branching_component_vanishes"), H("A genuinely pruned branching component vanishes"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let G be a finite connected cyclic flag graph with an actual cycle or two distinct protected anchor vertices, and let P be a genuine terminal leaf-pruning chronology. If any deleted incidence component has at least two original rotor-fixed flags at its removed owner vertices, then classOf G is zero in the actual rational AS, IHX and ordinary CL quotient. The proof constructs the actual open component and its trivalent placement, preserves its exact number of ordinary leaves, and invokes actual_branching_hair_vanishes through the completed literal HairTree representation. This closes the real leaf-pruning-to-local-vanishing bridge. It does not establish a connected graded source quotient comparison, the global core presentation, or the original four-loop claim."))), DescribeRole.Theorem))));
}
