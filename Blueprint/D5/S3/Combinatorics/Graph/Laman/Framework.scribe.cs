using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Laman;

internal sealed class FrameworkDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Laman/Framework.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Geometry/chen2026combinatorialrigidity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Real finite-dimensional frameworks and their edge rigidity maps.",
        H("Frameworks and rigidity rows"), Blocks(
            Describe.Lean(DescribeId.Create("framework-0"), DeclarationHandle.Create(Prefix + "Framework"),
                H("Framework placements"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("A framework on V in dimension d is a placement V → EuclideanSpace ℝ (Fin d)."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("framework-1"), DeclarationHandle.Create(Prefix + "edgeRow"),
                H("An edge row"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The row for an ordered pair u,v evaluates a motion x by the real inner product of the placement difference and motion difference."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("framework-2"), DeclarationHandle.Create(Prefix + "edgeRow_apply"),
                H("Edge-row evaluation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Evaluating edgeRow p u v at x gives ⟪p u − p v, x u − x v⟫ over ℝ."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("framework-3"), DeclarationHandle.Create(Prefix + "edgeRow_symm"),
                H("Edge-row orientation symmetry"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Swapping the endpoints leaves the edge row unchanged because both differences change sign."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("framework-4"), DeclarationHandle.Create(Prefix + "RigidityMap"),
                H("The rigidity map"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For a graph G and placement p, the rigidity map sends a motion to the family of edge-row values indexed by G.edgeSet."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("framework-5"), DeclarationHandle.Create(Prefix + "rigidityMap_apply"),
                H("Rigidity-map evaluation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("At an explicit edge s(u,v), the rigidity map component is the inner product ⟪p u − p v, p' u − p' v⟫ over ℝ."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("framework-6"), DeclarationHandle.Create(Prefix + "IsInfinitesimallyRigid"),
                H("Infinitesimal rigidity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("A finite graph is infinitesimally rigid at p when the real kernel of its rigidity map has finrank at most d(d+1)/2."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("framework-7"), DeclarationHandle.Create(Prefix + "IsGenericallyRigidInj"),
                H("Injectively generically rigid graphs"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("A finite graph is injectively generically rigid in dimension d when it has an infinitesimally rigid placement that is injective."))), DescribeRole.Definition)), []));
}
