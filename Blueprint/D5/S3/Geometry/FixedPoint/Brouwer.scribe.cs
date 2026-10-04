using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.FixedPoint;

internal sealed class BrouwerDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Geometry/mathxmum2025brouwer");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Continuous simplex self-maps have fixed points.",
        H("Continuous simplex self-maps have fixed points"),
        Blocks(Describe.Lean(
            DescribeId.Create("mathxmum-brouwer"),
            DeclarationHandle.Create("D5/S3/Geometry/FixedPoint/Brouwer.Brouwer"),
            H("Continuous simplex self-maps have fixed points"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(
                Paragraph(Text("For every positive natural n and continuous self-map of the real standard simplex indexed by Fin n, there exists x with f(x)=x. This includes the singleton simplex n=1. Continuity is the only analytic map hypothesis.")),
                Paragraph(Text("Color each lattice point by a coordinate not decreased by f. Scarf supplies colorful dominant cells. Coordinate estimates force their diameters to zero and coordinates outside a constant color set to zero. Finite pigeonhole and compactness give monotone subsequences. Points of each surviving color converge to the same limit; continuity gives coordinatewise inequalities, and the unit sums force equality.")),
                Paragraph(Text("The result and proof source are attributed to Math_XMUM's MIT-licensed Brouwer repository at its immutable revision. No mathematical novelty is claimed. The combinatorics and real fixed-point argument establish no tetrahedral geometry, marked gluing, trajectory invariance, uniqueness, geometric Hessian, or convergence conclusion."))),
            DescribeRole.Theorem))));
}
