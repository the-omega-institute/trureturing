using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Orthogonality;

internal sealed class OrthogonalitySymmetryObstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Orthogonality/OrthogonalitySymmetryObstruction.";
    private static DocumentBlock Item(string id, string declaration, string title,
        string text, DescribeRole role) => Describe.Lean(DescribeId.Create(id),
        DeclarationHandle.Create(Prefix + declaration), H(title),
        StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(
            LibraryNoteRef.Create("D5/L/QuadraticForms/binarysubspace2026complete")),
        Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual full orthogonal stabilizer obstruction.", H("The actual full orthogonal stabilizer obstruction"),
        Blocks(
            Item("stabilizer", "stabilizer", "The entire original group",
                "The actual subgroup of all linear automorphisms preserving the standard pairing and the original T is retained, with group closure and inverse proofs.", DescribeRole.Definition),
            Item("act", "act", "The action on every actual vertex",
                "Every nonzero six-coordinate Submodule, including the whole space, has the actual mapped-submodule action.", DescribeRole.Definition),
            Item("label-act", "labelAct", "The complete induced label action",
                "Every nonzero actual subspace of the original T is a label; no chosen subset of clique labels replaces this domain.", DescribeRole.Definition),
            Item("swap-element", "swapElement", "The received coordinate swap",
                "The transposition of the first two coordinates is orthogonal, belongs to the entire stabilizer and fixes T pointwise. It exchanges the actual adjacent lines with masks1 and2.", DescribeRole.Definition),
            Item("restricted", "restricted", "The complete restricted form",
                "Restrict the actual standard pairing to every full nonzero submodule, with no radical or vector omitted.", DescribeRole.Definition),
            Item("quotient-form", "quotientForm", "The actual nondegenerate quotient form",
                "Use the entire original radical quotient and its induced bilinear form. The generic radical-quotient owner proves nondegeneracy and transports the actual coordinate-swap isometry; no scalar or dimension proxy replaces the quotient.", DescribeRole.Definition),
            Item("profile-claim", "profileClaim", "The exact profile and quotient-isometry assertion",
                "The proposed proper coloring is constant whenever the full original dimension/K/H profile and actual radical-quotient isometry type agree. It quantifies every actual nonzero six-coordinate submodule.", DescribeRole.Definition),
            Item("symmetry-claim", "symmetryClaim", "The exact full-stabilizer assertions",
                "This disjunction uses the entire orthogonal stabilizer, its complete clique-label action, and all actual graph vertices. It asserts full equivariance or full invariance, not a restricted-subgroup condition.", DescribeRole.Definition),
            Item("claim", "claim", "The exact prohibited full-group assertion",
                "The combined prohibited assertion is the original profile/actual-quotient-only rule or either full-stabilizer coloring rule.", DescribeRole.Definition),
            Item("result", "result", "Refute full-stabilizer equivariance and invariance",
                "The original adjacent lines have equal full dimension/K/H data and isometric entire nondegenerate radical quotients. They also lie in one label-fixing orbit, contradicting properness for all three original proposed rules. This gives no obstruction to proper-subgroup symmetry or auxiliary coordinate choices; no new structural fifteen-color rule is asserted. The original plane/lift-feature obstruction is a separate remaining clause.", DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry")),
         DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/QuadraticForms/RadicalQuotientIsometry"))]));
}
