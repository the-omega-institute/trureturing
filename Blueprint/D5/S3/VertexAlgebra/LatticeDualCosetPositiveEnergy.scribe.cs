using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeDualCosetPositiveEnergyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual Original-Omega Energy Eigenspaces",
        H("Actual Original-Omega Energy Eigenspaces"),
        Blocks(
            Paragraph(Text("beta is integral, mu is rational with G_Q mu=beta, and H is a two-sided inverse of the original complex Gram matrix. The actual moduleL_0 eigenvalue of the unchanged full carrier basis is oscillatorEnergy(d)+q_mu(gamma). Exact duality gives q_mu(gamma)=q_mu(0)+chargeEnergy(gamma)+gamma dot beta. Relative to an attained minimum all basis weights differ by natural numbers. The sealed generic diagonal-tensor coefficient and eigenspace theorems are specialized to the scalar tensor unit; the actual action is retained. Full eigenspaces equal rational coefficient-support grades, and the entire exact fiber supplies their coordinates. Positive original Gram makes them finite dimensional. All statements concern algebraic vectors and point eigenvalues, with no Hilbert completion, analytic spectrum or self-adjointness claim.")),
            Paragraph(Text("Classical construction context: Bakalov-Kac, math/0402315v1, section 4.1. The imported Sugawara architecture retains Kalle Kytola's Apache-2.0 attribution and VirasoroProject revision 5ff4245383b2cdd4eea7a0524bc1274c32041eb4. The finite reductions and actual-action connections are native mathematical proofs; no external novelty is asserted.")),
            Describe.Lean(
                DescribeId.Create("latticedualcosetpositiveenergy-chargeweight-expansion"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeDualCosetPositiveEnergy.chargeWeight_expansion"),
                H("chargeWeight expansion"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact rational duality G mu=beta gives q_mu(gamma)=q_mu(0)+chargeEnergy(gamma)+gamma dot beta. Consequently charge-weight differences are integral."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticedualcosetpositiveenergy-weight-levels"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeDualCosetPositiveEnergy.weight_levels"),
                H("weight levels"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a globally minimizing charge gamma_0, every basis weight is q_mu(gamma_0)+n for an actual natural n. Nonnegativity turns the integral difference into a natural number."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticedualcosetpositiveenergy-modulel-basis-zero"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeDualCosetPositiveEnergy.moduleL_basis_zero"),
                H("moduleL basis zero"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under both original inverse equations and exact rational duality, ACTUAL L_0 of original omega acts on every unchanged carrierBasis(gamma,d) by oscillatorEnergy(d)+q_mu(gamma)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticedualcosetpositiveenergy-rationalgrade"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeDualCosetPositiveEnergy.rationalGrade"),
                H("rationalGrade"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The grade at rational e is exactly the submodule supported on all actual labels of weight e."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticedualcosetpositiveenergy-modulel-coeff"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeDualCosetPositiveEnergy.moduleL_coeff"),
                H("moduleL coeff"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary actual v and every label a, coeff(L_0 v,a)=cast(weight(a)) coeff(v,a). The generic diagonal-tensor theorem is used with scalar tensor factor Complex."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticedualcosetpositiveenergy-modulel-eigen-iff"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeDualCosetPositiveEnergy.moduleL_eigen_iff"),
                H("moduleL eigen iff"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every mixed or homogeneous actual v, L_0 v=cast(e)v if and only if v belongs to the rational coefficient grade at e. Both directions follow from the generic full-eigenspace supplier through the tensor unit."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticedualcosetpositiveenergy-gradecoeffequiv"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeDualCosetPositiveEnergy.gradeCoeffEquiv"),
                H("gradeCoeffEquiv"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The entire exact rational energy fiber parametrizes the grade by finitely supported complex coefficients, with no positivity needed for this equivalence."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticedualcosetpositiveenergy-eigenspace-finitedimensional"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeDualCosetPositiveEnergy.eigenspace_finiteDimensional"),
                H("eigenspace finiteDimensional"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Positive original Gram makes every actual L_0 eigenspace at a rational eigenvalue finite dimensional via its full exact fiber basis."))),
                DescribeRole.Theorem))));
}
