using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.BRST;

internal sealed class ActualLeechOrbifoldBRSTDocument : IScribeDocumentDefinition
{
    private static DocumentBlock Theorem(string name, string id, string title, string statement) =>
        Describe.Lean(DescribeId.Create("actual-leech-orbifold-brst-" + id),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldBRST." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(statement))), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The bosonic BRST charge for the actual orbifold is nilpotent and contracts at nonzero energy.",
        H("Actual Leech orbifold bosonic BRST"), Blocks(
            Paragraph(Text("The state carrier is the critical orbifold and hyperbolic lattice matter "
                + "tensored with the native bc ghost Fock space. E is the total Virasoro zero mode "
                + "and b₀ is the native zero antighost acting on this carrier.")),
            Theorem("Q_squared", "q-squared", "Nilpotence of the original charge",
                "Q² = 0 on the full tensor product, by the general square anomaly at central charge 26."),
            Theorem("differential_squared", "differential-squared", "Nilpotence on each eigenspace",
                "For every complex eigenvalue μ, the restriction d of Q to the μ-eigenspace of E "
                + "satisfies d² = 0."),
            Theorem("contraction", "contraction", "Explicit contraction at nonzero energy",
                "For every nonzero complex μ, h is the restriction of μ⁻¹b₀ to the μ-eigenspace "
                + "and d h + h d is the identity there. The zero-mode Ward identity gives "
                + "Q b₀ + b₀ Q = E."),
            Theorem("exact_of_closed", "exact-of-closed", "Primitive of a closed nonzero-energy state",
                "For every nonzero complex μ and state x with E x = μx and Q x = 0, "
                + "the specified primitive satisfies Q(μ⁻¹b₀ x) = x."))));
}
