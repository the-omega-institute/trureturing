using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class UmegakiConditionalBKMDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A uniform endpoint bound on the partial-trace kernel contracts conditional Umegaki divergence of faithful joint states.",
        H("Faithful conditional Umegaki contraction"), Blocks(
            Describe.Lean(DescribeId.Create("quantum-marginal-inverse-residual"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UmegakiConditionalBKM.quadratic_difference_eq_residual"),
                H("The joint and marginal inverse forms"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let P be ordinary partial trace over a nonempty finite local factor and let Z be positive definite on the joint finite matrix space. For a complex joint direction H and u in the closed unit interval, write M for the arithmetic interpolation of left and right multiplication. Set X = M(PZ,u) inverse applied to PH and V = H - M(Z,u)(X tensor I). The marginal transport identities give PV = 0. The joint inverse quadratic form of H minus the marginal form of PH equals the joint inverse quadratic form of V.")),
                    Paragraph(Text("Trace adjunction pairs an embedded reference matrix with the ordinary partial trace. Consequently the energy of X tensor I is the marginal quadratic form, and the cross term is twice that same form. The channel commutes with multiplication by embedded reference matrices on both sides and preserves P. The output residual is therefore the channel action applied to V, using the same X."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("faithful-conditional-relative-entropy-contraction"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UmegakiConditionalBKM.faithful_conditional_relativeEntropy_contraction"),
                H("The conditional divergence of faithful density states"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let N be a canonical finite quantum channel for which N(I) is positive definite, and let c lie in the closed unit interval. Assume that, for every finite reference R, positive definite joint Z and complex V with PV = 0, the endpoint inverse form of the amplified channel images is at most c times the input form. The endpoint is Re Tr(V adjoint Z inverse V), obtained from the native Hilbert–Schmidt inverse at u = 0.")),
                    Paragraph(Text("For every finite reference and pair of faithful joint density states rho and sigma, the difference between the output finite trace-log divergence and the divergence of the output reference marginals is at most c times the corresponding input difference. The states may be correlated and noncommuting and their reference marginals may differ. Positive definiteness of N(I) transports a positive floor to the joint output, and partial trace preserves faithfulness over the nonempty local factors. All four pairs lie in the finite support branch.")),
                    Paragraph(Text("For c < 1, the endpoint estimate applied at the reference center (PZ) inverse times P(Z PhiR(Y)) bounds the original trace infimum with multiplier k = c/(1-c). The common-state construction supplies both residual Gram inequalities at the same center. For the output inverse direction, weighted Cauchy–Schwarz gives q squared at most k times the energy defect times p, and q squared at most the uncentered input energy times p. Combining the estimates gives q at most c times p. The zero-output quadratic form is handled before cancellation. At c = 1 the uncentered estimate and the nonnegative defect give the bound directly.")),
                    Paragraph(Text("The residual identity turns the arithmetic-form estimate into a pointwise bound on joint-minus-marginal forms. Integration in u gives the corresponding logarithmic derivative estimate. The joint and marginal matrix paths each use the ordinary BKM formula with weight 1-t. Their trace corrections vanish for density states. The path integrals use the actual matrix logarithms and ordinary partial traces, including for correlated quantum references. The conclusion is confined to faithful endpoints."))),
                DescribeRole.Theorem))));
}
