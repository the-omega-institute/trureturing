using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Records;

internal sealed class PrimitiveRecordLeadingCoefficientDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveRecordLeadingCoefficient";
    private const string Title = "The leading cross matrix of the primitive periodic collision";
    private static LibraryNoteRef CollisionSource => LibraryNoteRef.Create("D5/L/Geometry/critchmorton2014mps");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title + ".", H(Title),
        Blocks(
            Claim("collisionLambda_eq", "The dominant mixed-transfer eigenvalue",
                "In the ket-first convention λ = (1+i)(3+√41). The other modes are "
                + "(1+i)(3−√41), 8i and −8. Their moduli are at most 8 and strictly below |λ|."),
            Claim("collisionPhaseRate", "The complex rate per site",
                "The rate γ = λ/√200 has modulus (3+√41)/10 and argument π/4.",
                DescribeRole.Definition),
            Claim("Sstar", "The exact coefficient matrix",
                "The 4 by 4 matrix S★ is written in the visible order 00, 01, 10, 11. "
                + "Its rows are (a,b,b,c), (d,e,f,d), (d,f,e,d), (c,b,b,a). For s = √41, "
                + "put δ = (25s−123)/656 and β = (697−75s)/1312. Then "
                + "a = 1/4+iδ, b = 3s/164+is/41, c = β−iδ, "
                + "d = 3s/164−is/41, e = 1/4−iδ and f = β+iδ.",
                DescribeRole.Definition),
            Claim("Sstar_mul_lambda_sq", "Readout of the dominant spectral projector",
                "For each visible pair p,q, λ² times S★[p,q] is the dominant insertion weight. "
                + "The proof reads the trace of the ket-first two-site insertion against the "
                + "mixed-transfer spectral projector. Splitting into Gaussian-integer and √41 "
                + "parts gives exact entry checks."),
            Claim("collision_flattening_cross_leading", "The cross reduction with its rate and phase removed",
                "Let Wᵦ be the normalized flattening of label b with two visible sites as rows "
                + "and m hidden sites as columns. For every visible entry p,q, "
                + "(W₀W₁†)[p,q]/γⁿ tends to S★[p,q] as m grows, with n = 2+m. "
                + "Division by γⁿ removes both the decay and the phase. The three other modes "
                + "vanish after dividing by the dominant mode."),
            Claim("Sstar_trace", "Trace of the leading matrix",
                "The exact matrix has tr S★ = 1. This fixes the leading trace amplitude "
                + "in the same phase convention."),
            Claim("Sstar_commutes_observed", "Commutation with the observed density",
                "The common marginal R = collisionMarginal satisfies RS★ = S★R. "
                + "This equality is checked directly on entries in the visible basis."),
            Claim("collision_weighted_coefficient", "Exact weighted Hilbert–Schmidt coefficient",
                "The Gaussian-integer and √41 arithmetic gives Re tr(R⁻¹ S★S★†)/2 "
                + "= (310625−46875√41)/16384, approximately 0.6395600201620616."),
            Claim("collision_weighted_coefficient_gt_half", "Strict excess over one half",
                "The exact weighted trace exceeds 1/2. The proof compares √41 with "
                + "302433/46875 by squaring. The verified scope is the matrix limit and "
                + "weighted trace. The complementary conditional-entropy and Helstrom "
                + "prefactors require separate analytic theorems."))));

    private static DocumentBlock Claim(string name, string title, string prose,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create("primitive-record-leading-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Module + "." + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(CollisionSource), Blocks(Paragraph(Text(prose))), role);
}
