using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class ForwardHockeyStickIntegralDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Divergence/ForwardHockeyStickIntegral";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite Umegaki pairing and its bounded Loewner difference in forward profiles.",
        H("Forward hockey-stick integrals"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("forward-profile"),
                DeclarationHandle.Create(Module + ".forwardProfile"),
                H("The forward hockey-stick profile"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For finite Hermitian matrices A and B of the same size, the profile at real s "
                    + "is the real trace of the positive part of A−sB."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("integral-forward-profile-eq-umegaki"),
                DeclarationHandle.Create(Module + ".integral_forwardProfile_eq_umegaki"),
                H("Two forward integrals for the trace-log pairing"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Divergence/frenkel2023integral"),
                    LibraryNoteRef.Create("D5/L/Divergence/hirchetomamichel2024quantum"),
                    LibraryNoteRef.Create("D5/L/Divergence/schmitt2026relative")),
                Blocks(
                    Paragraph(Text(
                        "For finite positive semidefinite A and positive definite B, let E(s) be "
                        + "the forward profile. Integrate (E(s)−Tr(A−sB))/s on (0,1) and E(s)/s on "
                        + "(1,∞). Both real integrands are integrable. The sum of the integrals plus "
                        + "Tr(A−B) is the real trace of A(log A−log B).")),
                    Paragraph(Text(
                        "The involution s ↦ s/(s−1) maps (0,1) onto (−∞,0) and (1,∞) onto "
                        + "itself. At t=s/(s−1), the pencil is (1−t)(A−sB). The scalar converts "
                        + "the negative-part trace into the forward profile on the right and the "
                        + "forward profile minus Tr(A−sB) on the left. The original weight, "
                        + "the factor |1−t|, and the Jacobian magnitude (s−1)⁻² multiply to 1/s. "
                        + "The pencil is positive semidefinite on [0,1]. Finiteness of the "
                        + "pencil integral gives integrability on both transformed tails.")),
                    Paragraph(Text(
                        "Frenkel’s Theorem 6 supplies the pencil formula. Hirche and Tomamichel’s "
                        + "Corollary 2.3 uses two orientations on the upper tail for states. "
                        + "Schmitt’s equations (36)–(38) include the unnormalized forward form."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("integral-forward-profile-sub-eq-umegaki-sub"),
                DeclarationHandle.Create(Module + ".integral_forwardProfile_sub_eq_umegaki_sub"),
                H("The signed profile difference on a bounded interval"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Divergence/jencova2024recoverability"),
                    LibraryNoteRef.Create("D5/L/Divergence/schmitt2026relative")),
                Blocks(
                    Paragraph(Text(
                        "Take two finite pairs (A,B) and (C,D) with positive semidefinite first "
                        + "endpoints and positive definite references. Their dimensions may differ. "
                        + "Suppose Tr A=Tr C, Tr B=Tr D, 0<u≤v, uB≤A≤vB, and uD≤C≤vD. "
                        + "The profiles agree for s≤u, where each equals its affine trace, and "
                        + "for s≥v, where both vanish. Their difference divided by s is integrable "
                        + "on [u,v]. Its real integral is the first trace-log pairing minus the second.")),
                    Paragraph(Text(
                        "The matching trace masses cancel both the affine term in the lower "
                        + "integrand and the additive trace correction. Jenčová’s Corollary 1 "
                        + "gives the normalized finite-interval formula. The signed identity yields "
                        + "the profile comparison for the Fibonacci optimization."))),
                DescribeRole.Theorem))));
}
