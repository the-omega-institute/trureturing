using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Mechanical;

internal sealed class RotationObservationCellsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Mechanical/RotationObservationCells.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual rotation readouts determine half-open phase cells, sharp phase decoders, and a unique new split.",
        H("Rotation Observation Cells"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("rotation-observation-prefix"),
                DeclarationHandle.Create(Prefix + "rotationPrefix"),
                H("Actual window observations"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The binary word evaluates the indicator of [1-alpha,1) on the actual fractional iterates x+k*alpha. This is an observable on phases, rather than an abstract supplied partition."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("rotation-observation-cell-decoder"),
                DeclarationHandle.Create(Prefix + "rotation_prefix_cell_and_decoder"),
                H("Exact fibers and all uniform decoders"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every irrational slope in [0,1), every prefix length and every sorted rotation arc, the actual observation fiber of its left endpoint is exactly that half-open arc. Every center and radius valid on the observed word is then characterized by b-radius <= center <= a+radius. The proof identifies bits with the existing mechanical word, reconstructs cumulative floors, proves equivalence with every rotation-cut test, and only then uses the sorted-arc owner. The radius lower bound handles the excluded right endpoint by an interior contradiction. No cylinder estimate or phase-decoding guarantee is a premise."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rotation-observation-unique-split"),
                DeclarationHandle.Create(Prefix + "rotation_prefix_single_cut"),
                H("A unique cell is split by the next observation"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An additional actual bit adds exactly the threshold at fractional part -(n+1)*alpha to the old equality test. Irrationality proves this cut is absent from the old boundary set, so it lies strictly inside a unique old arc. Explicit phases on its two sides have equal old words and different extended words. Pairwise disjointness proves uniqueness; no list-refinement history is assumed. This establishes the geometric input needed for subsequent entropy and decision-risk consumers. Classical Sturmian complexity and the three-gap theorem are prior background, not claims of new discovery."))),
                DescribeRole.Theorem))));
}
