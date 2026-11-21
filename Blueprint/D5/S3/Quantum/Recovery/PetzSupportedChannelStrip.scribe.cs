using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class PetzSupportedChannelStripDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two integrable boundary deficits of the actual supported channel overlap sum to its trace-log entropy loss.",
        H("The supported-channel Petz strip identity"),
        Blocks(
            Paragraph(Text("Let Φ be a quantum channel between nonempty finite matrix spaces, and let ρ and σ be input density states. Given a supported relative modular model M for Φ, ρ and σ, write D = M.data. The input coordinates (j,i) and output coordinates (l,k) range over the positive eigenvalues of the reference and source states on the corresponding spaces. Put a(j,i) = s(j)/r(i) and b(l,k) = q(l)/p(k), let V be the matrix of the channel adjoint in weighted mixed eigenvector coordinates, and let ξ and η be the normalized input and output source vectors. For any real diagonal d on finite coordinates, its modular power P(d,z) has diagonal exp(log(d) z). The amplitude γ(z) is P(a,z) V P(b,−z) η. The finite overlap F(z) sums conj(ξ(x)) V(x,y) η(y) exp((log(a(x)) − log(b(y))) z) over input and output coordinates x and y. Write δ(r,s) = 2(1 − Re F(r + i s)).")),
            Result("overlap-derivative", "hasDerivAt_overlap_zero", "Trace-log derivative",
                "For any M, F has complex derivative at zero equal to the negative real trace-log relative entropy loss embedded in ℂ. The two logarithms in the finite frequency yield the input and output modular log expectations, and the adjoint identity sends the output term to the η expectation."),
            Result("deficit-distance", "deficit_eq_distance_add_defect", "Squared distance and lost norm",
                "For any M and real r and s, δ(r,s) equals the sum over input coordinates x of |ξ(x) − γ(r + i s)(x)|², plus one minus the sum over x of |γ(r + i s)(x)|²."),
            Result("lower-deficit-nonneg", "lower_deficit_nonneg", "Lower boundary deficit",
                "For any M and real s, δ(0,s) ≥ 0. The imaginary powers are unitary on the supported coordinates and V is a contraction."),
            Result("upper-deficit-nonneg", "upper_deficit_nonneg", "Upper boundary deficit",
                "For any M and real s, δ(1/2,s) ≥ 0. The imaginary powers act on the two sides of the upper comparison contraction."),
            Describe.Lean(
                DescribeId.Create("petz-integral-supported-channel-strip"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/PetzSupportedChannelStrip.integral_supported_channel_strip"),
                H("Integrable physical boundary deficits"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Divergence/yang2026quantumdataprocessing")),
                Blocks(
                    Paragraph(Text("For every supported relative modular model M, use the same data D = M.data on both boundaries. The function s ↦ lowerWeight(s) δ(0,s) is Lebesgue integrable on ℝ. The function s ↦ petzWeight(s) δ(1/2,s) is Lebesgue integrable on ℝ. The sum of the two whole-line integrals equals the trace-log relative entropy of ρ with respect to σ minus the trace-log relative entropy of Φ(ρ) with respect to Φ(σ). The lower weight is π/(cosh(2πs) − 1), with the totalized value at zero, and the upper weight is π/(cosh(2πs) + 1). Both integrands use the unsymmetrized overlap.")),
                    Paragraph(Text("For an actual channel Φ and any input pair with support : SupportContained ρ σ, set M = supported_relative_modular_model Φ ρ σ support and apply integral_supported_channel_strip M. Both integrands then use the canonical supported data of that channel and pair. The constructor obtains output support containment from the input hypothesis, so the application includes singular input and output states.")),
                    Paragraph(Text("Yang’s Theorem II.1 gives the entropy-loss strip identity for faithful states. Section V.3 proposes the finite-dimensional extension under support containment. In the supported matrix model, normalization and the lower contraction verify the hypotheses of the finite exponential strip theorem at the singular boundary. The trace-log derivative identifies its right-hand side. The upper-edge contraction gives pointwise upper nonnegativity, and the finite exponential bound supplies upper integrability."))),
                DescribeRole.Theorem))));

    private static DocumentBlock.Describe Result(string id, string declaration, string heading, string statement) =>
        Describe.Lean(
            DescribeId.Create($"petz-strip-{id}"),
            DeclarationHandle.Create($"D5/S3/Quantum/Recovery/PetzSupportedChannelStrip.{declaration}"),
            H(heading),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(statement))),
            DescribeRole.Theorem);
}
