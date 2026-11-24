using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.BRST;

internal sealed class ActualLeechOrbifoldRelativeNormTwoDocument : IScribeDocumentDefinition
{
    private static DocumentBlock Theorem(string name, string id, string title, string statement) =>
        Describe.Lean(DescribeId.Create("actual-leech-orbifold-relative-norm-two-" + id),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRelativeNormTwo." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(statement))), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual norm-two absolute shell has two coordinates and the relative shell is a line.",
        H("Actual Leech orbifold norm-two BRST shell"), Blocks(
            Paragraph(Text("The momentum p = (1, 1) lies in the standalone hyperbolic plane. "
                + "The ground states ψ and ψ₁₃ use the orbifold vacuum and the plane state eᵖ, "
                + "with ghost occupations {1} and {1, 3} respectively. The coefficients ρ and σ "
                + "read these states in the fixed sector.")),
            Theorem("mem_absoluteShell_iff", "absolute-shell", "Absolute shell",
                "A state x has momentum p and zero total energy exactly when "
                + "x = ρ(x)ψ + σ(x)ψ₁₃. The positive twisted weight excludes the entire twisted sector."),
            Theorem("absoluteProjection_eq", "projection-fixed", "Fixed points of the projector",
                "The projector P defined by those two coefficients fixes exactly the absolute shell."),
            Theorem("absoluteProjection_actions", "projection-actions", "Projector identities",
                "On the full state space P² = P, EP = PE = 0, and PΠₚ = P, "
                + "where E is the total Virasoro zero mode and Πₚ selects momentum p."),
            Theorem("rho_b0", "antighost-coordinate", "Zero antighost coordinate",
                "On every state x in the full tensor product, ρ(b₀ x) = −σ(x)."),
            Theorem("normTwo_relative_shell", "relative-shell", "Relative shell and charge",
                "The intersection C of the absolute shell with the kernel of b₀ is the complex span of ψ. "
                + "The native ghost number satisfies Nψ = ψ and the actual BRST charge Q vanishes on C."))));
}
