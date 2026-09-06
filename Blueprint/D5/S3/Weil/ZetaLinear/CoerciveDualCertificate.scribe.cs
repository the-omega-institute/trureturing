using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaLinear;

internal sealed class CoerciveDualCertificateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A full residual turns any trial vector into a certified energy-dual readout bound on a complex operator domain.",
        H("Coercive Dual Certificate"),
        Blocks(
            Describe.Lean(DescribeId.Create("domain-energy"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaLinear/CoerciveDualCertificate.domainEnergy"), H("Actual domain energy"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The real part of the actual domain pairing. Boundedness or an inverse operator is not built into this definition."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("full-residual"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaLinear/CoerciveDualCertificate.dualResidual"), H("Full candidate-adjusted residual"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Removes a candidate-direction term from g-Mv. For a unit candidate this is the orthogonal projection. All omitted Hilbert-space modes remain in its norm."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("dual-budget"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaLinear/CoerciveDualCertificate.dualBudget"), H("Residual-certified coefficient"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Combines the signed trial objective with the full residual norm squared divided by coercivity. No exact dual solution is required."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("variational-upper"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaLinear/CoerciveDualCertificate.dual_variational_upper"), H("Global variational upper certificate"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Completes the actual complex-domain energy around any orthogonal trial, retaining both mixed terms, and controls the remaining objective by coercivity and the full residual."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("energy-readout"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaLinear/CoerciveDualCertificate.dual_energy_readout"), H("Certified energy-weighted readout"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Proves nonnegativity of the coefficient and the squared readout bound for every orthogonal domain vector. A complex scaled test converts the variational bound into the energy-dual inequality. No completeness, cutoff, or exact inverse is assumed."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exact-optimality"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaLinear/CoerciveDualCertificate.exact_dual_budget_optimal"), H("Exact dual optimality when attained"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("When the full projected residual vanishes and the trial image is nonzero, the coefficient equals its actual energy and is a lower bound for every valid global energy-readout coefficient. Existence of such a trial is not asserted."))), DescribeRole.Theorem)),
        []));
}
