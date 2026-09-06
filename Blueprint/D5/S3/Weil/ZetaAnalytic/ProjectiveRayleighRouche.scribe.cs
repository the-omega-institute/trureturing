using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaAnalytic;

internal sealed class ProjectiveRayleighRoucheDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaAnalytic/ProjectiveRayleighRouche.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A proved projective Rayleigh error passes through actual bounded linear readouts "
            + "and supplies the error term of the existing rectangle Rouche theorem.",
        H("Projective Rayleigh Enclosure and Rectangle Zero Counts"), Blocks(
            Describe.Lean(
                DescribeId.Create("bounded-linear-projective-error-squared"),
                DeclarationHandle.Create(Owner + "bounded_linear_readout_error_sq"),
                H("Propagate a squared Hilbert-space error"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a bounded complex linear functional L, the existing operator-norm "
                    + "inequality bounds ||Lx-Ly|| by ||L|| ||x-y||. Squaring preserves the "
                    + "inequality because both sides are nonnegative. Thus an actual squared "
                    + "state-error bound r gives ||Lx-Ly||^2<=||L||^2 r. This is a companion "
                    + "transport lemma, with no claim of an independent analytical discovery."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bounded-linear-strict-rouche-boundary"),
                DeclarationHandle.Create(Owner + "bounded_linear_readout_rouche_bound"),
                H("A separately certified boundary margin makes the comparison strict"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The explicit inequality ||L||^2 r < ||Ly||^2 supplies strictness. "
                    + "The result is precisely ||Lx-Ly||<||Ly||, the pointwise hypothesis "
                    + "consumed by the rectangle zero-count owner. A small state error alone "
                    + "does not imply that Ly is nonzero or provide this boundary margin."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("projective-enclosure-rectangle-zero-count"),
                DeclarationHandle.Create(Owner + "projective_rayleigh_rectangle_zero_count"),
                H("Consume the derived projective estimate in the existing zero count"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The operator-domain hypotheses are passed directly to "
                    + "projective_rayleigh_enclosure; no projective error bound is assumed. "
                    + "The proved overlap is nonzero. At each rectangle boundary point the "
                    + "bounded readout transfers the derived ratio (U-ell)/(T-ell) to a "
                    + "strict Rouche inequality. The existing "
                    + "rectangle_zero_count_eq_of_norm_sub_lt then identifies the two sums "
                    + "of analytic multiplicities. Both functions' analyticity, their exact "
                    + "finite zero lists and the candidate boundary margin remain explicit."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "The intended arithmetic application uses Fourier evaluation on an actual "
                + "fixed-support L2 space. Realizing that bounded functional, its norm bound "
                + "and its analytic dependence is still separate work. This source does not "
                + "identify an arbitrary readout with Xi, certify a zero-free rectangle, "
                + "or prove uniform convergence as the support radius grows.")),
            Paragraph(Text(
                "This is a named downstream consumer of the new variational theorem and of "
                + "the existing RoucheZeroCount module. The latter remains the sole owner of "
                + "rectangle zero-count stability; no second zero predicate or multiplicity "
                + "definition is introduced. The companion assembly is not counted as a "
                + "separate solution of an open problem."))
        )));
}
