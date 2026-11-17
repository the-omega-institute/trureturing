using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class UmegakiRareFlagBKMDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rectangular rare flag logarithmic derivative has the BKM logarithmic asymptotic.",
        H("Rare flag BKM limit"), Blocks(
            Describe.Lean(DescribeId.Create("rare-flag-log-deriv-limit"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UmegakiRareFlagBKM.rare_flag_logDeriv_limit"),
                H("The actual resolvent limit"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For arbitrary finite index types iota and kappa, positive definite complex matrices Z and C, and an arbitrary rectangular complex matrix V, set B(delta)=fromBlocks Z 0 0 (delta smul C) and H=fromBlocks 0 V Vᴴ 0. The theorem takes the real trace of Hᴴ times the actual Bochner-integral LogDerivTrace.logDeriv(B(delta),H), divides by 2 log(1/delta), and gives the right-filter limit at delta=0 as Re Tr(Vᴴ Z⁻¹ V).")),
                    Paragraph(Text("The proof retains both off-diagonal blocks, diagonalizes Z and C independently, evaluates the finite resolvent pair kernels, and treats coincident eigenvalues before the separated singular branch. Empty carriers and V=0 remain in scope through the finite sums. No normalization, commutation, common eigenbasis, unital output, coefficient equality, or novelty claim is asserted.")),
                    Paragraph(Text("This is a reusable support theorem for the rare-reference lower-bound route in the conditional Umegaki problem. It does not construct admissible density-state pairs, prove c0 <= eta_c, establish an all-channel support condition, or settle the external open problem."))),
                DescribeRole.Theorem))));
}
