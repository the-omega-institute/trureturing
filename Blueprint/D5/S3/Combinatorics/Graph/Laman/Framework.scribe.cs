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
                Blocks(Paragraph(Text("A framework on V in dimension d is a placement V to EuclideanSpace ℝ (Fin d)."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("framework-1"), DeclarationHandle.Create(Prefix + "edgeRow"),
                H("An edge row"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The row for an ordered pair u,v evaluates a motion x by the real inner product of the placement difference and motion difference."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("framework-2"), DeclarationHandle.Create(Prefix + "edgeRow_apply"),
                H("Edge-row evaluation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Evaluating edgeRow p u v at x gives the real inner product of the two differences."))), DescribeRole.Theorem),
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
                Blocks(Paragraph(Text("At an explicit edge s(u,v), the rigidity map component is the real inner product of placement and motion differences."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("framework-6"), DeclarationHandle.Create(Prefix + "continuous_rigidityMap_apply"),
                H("Continuity of a rigidity component"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For a fixed motion and edge, the rigidity-map component is continuous as a function of the placement."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("framework-7"), DeclarationHandle.Create(Prefix + "rigidityMap_ker_mono"),
                H("Kernel monotonicity under edge inclusion"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Adding graph edges can only shrink the rigidity-map kernel."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("framework-8"), DeclarationHandle.Create(Prefix + "rigidityMap_finrank_range_le"),
                H("Range rank bounded by edge count"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For a finite vertex type, the real finrank of the rigidity-map range is at most the number of graph edges."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("framework-9"), DeclarationHandle.Create(Prefix + "IsInfinitesimallyRigid"),
                H("Infinitesimal rigidity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("A finite graph is infinitesimally rigid at p when the real kernel of its rigidity map has finrank at most d(d+1)/2."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("framework-10"), DeclarationHandle.Create(Prefix + "IsGenericallyRigid"),
                H("Generic rigidity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("A finite graph is generically rigid in dimension d when some placement is infinitesimally rigid."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("framework-11"), DeclarationHandle.Create(Prefix + "IsGenericallyRigidInj"),
                H("Injectively generically rigid graphs"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("A finite graph is injectively generically rigid in dimension d when it has an infinitesimally rigid placement that is injective."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("framework-12"), DeclarationHandle.Create(Prefix + "top_fin_two_isGenericallyRigidInj"),
                H("The two-vertex injective base"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The complete graph on two vertices has an injectively generically rigid placement in every positive dimension."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("framework-13"), DeclarationHandle.Create(Prefix + "top_fin_two_isGenericallyRigid"),
                H("The two-vertex base"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The complete graph on two vertices is generically rigid in every dimension."))), DescribeRole.Theorem )), []));}
