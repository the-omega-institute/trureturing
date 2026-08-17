using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumContext;

internal sealed class CompleteBasisReconstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete complementary basis probabilities reconstruct a trace-one matrix.",
        H("Complete Complementary-Basis Reconstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("complete-basis-reconstruction"),
                DeclarationHandle.Create(
                    "D5/S3/QuantumContext/CompleteBasisReconstruction."
                        + "complete_basis_reconstruction"),
                H("Complete complementary bases reconstruct the state"),
                StatementSource.FromAuthor(Disp(Seq(
                    Rho, Sp, Eq, Sp, Frac, Grp(F.Id("I")), Grp(F.Id("d")),
                    Sp, Plus, Sp,
                    Sum, Underscore, Grp(Ell, Sp, InMacro, Sp, F.Id("L")), Sp,
                    Sum, Underscore, Grp(F.Id("j"), Sp, InMacro, Sp, F.Id("d")), Sp,
                    Open, F.Id("p"), Underscore, Grp(Ell, Sp, F.Id("j")), Sp, Minus, Sp,
                    Frac, Grp(D(1)), Grp(F.Id("d")), Close, Sp,
                    F.Id("P"), Underscore, Grp(F.Id("j")), Caret,
                    Grp(Mathcal, Grp(F.Id("B")), Underscore, Grp(Ell)), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let P(l,j) be the rank-one outcome projectors of a complete family "
                            + "of pairwise mutually unbiased bases, and let p(l,j) be the real "
                            + "probability Tr(rho P(l,j)). Each basis resolves the identity, and "
                            + "the projector trace overlap is one on the same outcome, zero on "
                            + "different outcomes of one basis, and one over d across bases.")),
                    Paragraph(Text(
                        "The completeness premise is the preceding tomography theorem's precise "
                            + "conclusion: equality of all selected projector traces determines "
                            + "the matrix. The proof evaluates the displayed candidate against "
                            + "every projector. Centered coefficients sum to zero within each "
                            + "basis, so all other-basis contributions cancel and the matching "
                            + "basis contributes exactly p(l,j).")),
                    Paragraph(Text(
                        "Pinned Mathlib has no packaged mutually unbiased-basis reconstruction "
                            + "theorem. The proof directly applies its matrix sum, scalar, and "
                            + "trace identities. Positivity and Hermiticity of rho are not needed "
                            + "after the density-state trace-one condition and the real Born "
                            + "probabilities have been supplied."))),
                DescribeRole.Theorem))));
}
