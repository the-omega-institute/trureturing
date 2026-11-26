using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix.Jacobi;

internal sealed class SharpProbeTransferDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/Jacobi/SharpProbeTransfer";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two full endpoint resolvent columns characterize agreement on the initial Jacobi component.",
        H("Sharp probe count for the Jacobi endpoint Green column"),
        Blocks(
            Item("EndpointConnected", "Initial Jacobi component",
                "A site j belongs to the initial component when every lower bond strictly before j is nonzero. "
                + "Site zero always belongs. If a bond vanishes, the component ends at the site before "
                + "the first such bond.",
                DescribeRole.Definition),
            Item("adjacent_green_minor", "Adjacent Green minor",
                "Let H be a complex tridiagonal matrix of positive size and assume every principal tail "
                + "of each of the two shifts z₀I−H and z₁I−H is invertible. Write g(z) for the full first "
                + "inverse column and mᵢ(z) for the first diagonal entry of the inverse of the tail starting at i. "
                + "At consecutive sites p,i, the determinant gₚ(z₀)gᵢ(z₁)−gₚ(z₁)gᵢ(z₀) factors as "
                + "gₚ(z₀)gₚ(z₁)bₚ(mᵢ(z₁)−mᵢ(z₀)), where bₚ is the lower bond at p. "
                + "This follows by applying the Green-column transfer at each probe, including when bₚ vanishes."),
            Item("two_probe_eq_iff", "Exact detection by two opposite-half-plane probes",
                "Let H₀ and H₁ be Hermitian complex matrices of the same positive size, with H₀ and the "
                + "difference V=H₁−H₀ tridiagonal. Fix z₀ with positive imaginary part and z₁ with negative "
                + "imaginary part. The full first inverse columns of the shifted H₀ and H₁ coincide at both "
                + "probes exactly when V has zero columns at every site of the initial component of H₀. "
                + "Nonreal shifts and their Hermitian compressions are invertible. Their inverse diagonal "
                + "imaginary parts have signs opposite to the probe's imaginary part, making the adjacent "
                + "Green minor nonzero inside the component. The column equations reduce agreement to Vg(z)=0. "
                + "Induction over the component eliminates earlier columns. In the first row past a zero "
                + "bond only the last connected site can contribute, so the boundary entry also vanishes. "
                + "Conversely, each reference Green column vanishes outside the initial component."),
            Item("firstColumn_eq_of_two_probes", "Agreement at every nonreal probe",
                "Under the Hermiticity and tridiagonal support hypotheses, equality of the full first inverse "
                + "columns at a probe with positive imaginary part and a probe with negative imaginary part "
                + "implies equality at each nonreal spectral parameter. The two samples force V to vanish "
                + "on the initial component, which supports the reference column at every such parameter."),
            Item("twoSiteReference", "Two-site reference",
                "The reference has zero diagonal and both off-diagonal entries equal to the real bond b.",
                DescribeRole.Definition),
            Item("twoSitePerturbation", "Two-site perturbation",
                "For real b and ε and complex z, the perturbation is ε times the outer product of "
                + "x=(b,−conjugate(z)) with its conjugate transpose.",
                DescribeRole.Definition),
            Item("one_probe_two_site_adversary", "A counterexample at any prescribed single probe",
                "Fix a complex z with nonzero imaginary part, any nonzero real b and any positive real ε. "
                + "For the two-site reference H₀ and the perturbation V above, H₀ and H₁=H₀+V are Hermitian. "
                + "Both H₀ and V are tridiagonal, and both sites belong to the initial component of H₀. "
                + "Their full first inverse columns agree at z even though V(0,0) is nonzero. The second row "
                + "of the reference column equation gives orthogonality to x, so V annihilates the observed column.")
        )));

    private static DocumentBlock Item(string name, string title, string explanation,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Module + "." + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(explanation))), role);
}
