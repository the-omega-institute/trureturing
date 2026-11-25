using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CharacterSums;

internal sealed class DirichletCyclicLaplaceDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/CharacterSums/DirichletCyclicLaplace.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual cyclic character Laplace transform",
        H("The actual cyclic character Laplace transform"),
        Blocks(
            Paragraph(Text("The selected length r may be any natural number at most "
                + "the order of chi; all selected positive powers are nonprincipal.")),
            Paragraph(Text("Let chi be a Dirichlet character modulo a positive integer, and let "
                + "r be at most its order. The cyclic family uses the actual Mangoldt ramp, "
                + "the zeta "
                + "remainder U, and the real parts of the nontrivial powers of chi. All "
                + "integrals below converge absolutely when the real part of s exceeds one.")),
            Describe.Lean(DescribeId.Create("character-half-plane-transform"),
                DeclarationHandle.Create(Module + "characterRamp_half_plane_laplace"),
                H("The twisted Mangoldt transform"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The twisted von Mangoldt Dirichlet series gives the "
                    + "negative logarithmic derivative of the actual Dirichlet L-function, "
                    + "divided by s times (s minus one). Absolute convergence permits the "
                    + "series and integral to be exchanged. This identity applies to every "
                    + "character, including the principal one, for every s with real "
                    + "part greater than one. The integral is over positive y with "
                    + "kernel exp(-s y) and ramp evaluated at exp y."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cyclic-half-plane-transform"),
                DeclarationHandle.Create(Module + "gl1CyclicFamily_half_plane_laplace"),
                H("The full cyclic transform"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The zeta term is its corrected logarithmic derivative. "
                    + "Each character contribution is one half of its transform at s plus "
                    + "the conjugate of its transform at conjugate s. The weights are "
                    + "one divided by three r plus one. This formula has no hypotheses "
                    + "about zeros, residues, or asymptotic estimates. More precisely, for "
                    + "r at most the order of chi and real part of s greater than one, "
                    + "the cyclic integrand is integrable on the positive y-axis, and "
                    + "its integral equals cyclicTransform chi s."))),
                DescribeRole.Theorem))));

}
