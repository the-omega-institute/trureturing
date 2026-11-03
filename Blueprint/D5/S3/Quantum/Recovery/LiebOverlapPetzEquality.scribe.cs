using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class LiebOverlapPetzEqualityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One fixed completed Petz channel characterizes actual overlap and entropy equality.",
        H("Lieb overlap equality and a fixed Petz recovery"), Blocks(
            Describe.Lean(
                DescribeId.Create("actual-lieb-overlap-equality-iff-fixed-petz-recovery"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/LiebOverlapPetzEquality.actual_lieb_overlap_equality_iff_fixed_petz_recovery"),
                H("One recovery before choosing the state or the power"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Divergence/meiburg2026relative")),
                Blocks(Paragraph(Text("Fix a channel Phi between finite nonempty quantum systems and a density "
                    + "sigma. Choose the completed Petz channel from this pair, with its displayed full-matrix "
                    + "action: the usual spectral-pseudoinverse Petz core plus a reset to sigma on the "
                    + "orthogonal complement of the support of Phi(sigma). This one channel recovers sigma. "
                    + "For every rho supported by sigma and every 0<q<1, equality of the actual physical "
                    + "overlaps Tr(rho^(1-q) sigma^q) before and after Phi is equivalent both to equality "
                    + "of finite trace-log relative entropy and to recovery of rho by that same channel. "
                    + "The choice of recovery precedes rho and q; it is independent of both. Singular "
                    + "density matrices are allowed, without a spectral floor or ratio bound. "
                    + "Consequently, for a fixed channel and pair of states, equality at any one "
                    + "interior power forces equality at every interior power: each is equivalent "
                    + "to the same recovery equation.")),
                    Paragraph(Text("The forward proof uses the full weighted resolvent-energy budget. "
                    + "Overlap equality forces the nonnegative integral to vanish. Since its weight is "
                    + "strictly positive and the resolvent error is continuous on the positive axis, the "
                    + "error vanishes at every positive shift. Norm saturation supplies the adjoint "
                    + "identity, giving zero scalar resolvent defects; the existing functional-rigidity "
                    + "theorem then gives the logarithmic identity and actual entropy equality. The "
                    + "converse applies actual overlap monotonicity to Phi and to the already fixed "
                    + "recovery channel. The existing fixed-reference Petz equality theorem completes "
                    + "both equivalences.")),
                    Paragraph(Text("This is the Petz sufficiency equality mechanism for power "
                    + "quasi-entropies; no literature novelty, quantitative trace-distance estimate, "
                    + "q=0 or q=1 endpoint, or unsupported infinite-entropy equivalence is claimed. "
                    + "For classical source context see Hiai-Mosonyi-Petz-Beny, Quantum f-divergences "
                    + "and error correction, arXiv:1008.2529, Theorem 5.1. The current derivation uses "
                    + "the project's actual overlap budget and its existing fixed Petz channel."))),
                DescribeRole.Theorem))));
}
