using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumContext;

internal sealed class ProjectionValuationObstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An exact eighteen-ray parity configuration obstructs binary projection valuations.",
        H("An Eighteen-Ray Projection-Valuation Obstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nine-complete-contexts-have-no-binary-projection-valuation"),
                DeclarationHandle.Create("D5/S3/QuantumContext/ProjectionValuationObstruction.projection_valuation_obstruction"),
                H("Nine complete contexts have no binary projection valuation"),
                StatementSource.FromAuthor(Disp(Seq(
                    Neg, Sp, Exists, Sp, F.Id("v"), Colon, Sp, F.Id("P"), To, Sp,
                    OpenBrace, D(0), Comma, D(1), CloseBrace, Comma, Esc,
                    Forall, Sp, F.Id("c"), InMacro, Sp, F.Id("C"), Comma, Esc,
                    Sum, Underscore, Grp(F.Id("p"), Sp, InMacro, Sp, F.Id("C"),
                        Underscore, Grp(F.Id("c"))), Sp,
                    F.Id("v"), Open, Sp, F.Id("p"), Close, Eq, D(1), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The configuration consists of eighteen explicit integer ray "
                            + "representatives in complex dimension four and nine tetrads. "
                            + "The declarations ks_vectors_injective, ks_vectors_nonzero, and "
                            + "ray_norm_sq_exact audit the ray table. The exact integer code "
                            + "projectionCode is four times each normalized outer product. "
                            + "Kernel-checked integer identities then give trace one, "
                            + "nonzero, self-adjoint, and idempotent complex projections.")),
                    Paragraph(Text(
                        "Every context map is injective. Its four rays are pairwise "
                            + "orthogonal, the corresponding projection products vanish, and "
                            + "the four projections sum exactly to the identity. The finite "
                            + "incidence certificate proves that every ray occurs in exactly "
                            + "two of the thirty-six context slots. The theorem "
                            + "projection_injective proves that the eighteen rank-one "
                            + "projections are pairwise distinct; ConfigurationProjection is "
                            + "their range, and labeledProjection embeds the ray table into it.")),
                    Paragraph(Text(
                        "A binary valuation selecting exactly one projection in each context would "
                        + "make the sum of the nine context totals equal to nine. Regrouping "
                        + "the same terms by ray makes every contribution occur twice, so "
                        + "the total is even. The Lean proof exposes the nine exact equations "
                        + "and closes this parity contradiction arithmetically; it does not "
                        + "enumerate all binary functions or use an unchecked evaluator.")),
                    Paragraph(
                        Text(
                            "The general contextual obstruction is classical background; "),
                        Ref("D5/L/kochen1968problem"),
                        Text(
                            " records that scope. The deposited theorem is the exact finite "
                            + "dimension-four projective certificate above: an instance-level "
                            + "obstruction on valuations of these actual projections. It does "
                            + "not assert the full "
                            + "classification in every dimension at least three, a Gleason "
                            + "representation theorem, or a qubit projection obstruction."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-first-eight-contexts-have-an-explicit-valuation"),
                DeclarationHandle.Create("D5/S3/QuantumContext/ProjectionValuationObstruction.eight_contexts_satisfiable"),
                H("The first eight contexts have an explicit valuation"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("eightContextValuation"), Eq, Open,
                    D(0), Comma, D(1), Comma, D(0), Comma, D(0), Comma,
                    D(1), Comma, D(0), Comma, D(0), Comma, D(0), Comma,
                    D(0), Comma, D(1), Comma, D(0), Comma, D(1), Comma,
                    D(0), Comma, D(0), Comma, D(0), Comma, D(0), Comma,
                    D(0), Comma, D(0), Close, Comma, Esc,
                    Forall, Sp, F.Id("c"), Lt, D(8), Comma, Esc,
                    Sum, Underscore, Grp(F.Id("r"), Sp, InMacro, Sp, F.Id("C"),
                        Underscore, Grp(F.Id("c"))), Sp,
                    F.Id("eightContextValuation"), Open, Sp, F.Id("r"), Close,
                    Eq, D(1), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The explicit valuation selecting zero-based ray labels 1, 4, 9, "
                        + "and 11 gives total one in each of the first eight contexts. Its "
                        + "total in the ninth context is zero. Thus the local constraints "
                        + "are nonempty and remain jointly satisfiable until the final "
                        + "tetrad closes the odd parity cycle; the obstruction is not a "
                        + "consequence of an empty index family or malformed context data."))),
                DescribeRole.Theorem))));
}
