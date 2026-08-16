using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Sharpness;

internal sealed class ExceptionalPointOverlapDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normalized overlap of the two explicit PT branches is the smaller coupling ratio.",
        H("Exceptional-Point Branch Overlap"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exceptional-point-branch-overlap"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Sharpness/ExceptionalPointOverlap."
                    + "exceptional_point_branch_overlap"),
                H("The PT branch overlap is the smaller coupling ratio"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("delta"), Comma, F.Id("kappa"), Sp, InMacro, Sp,
                    Mathbb, Grp(F.Id("R")), Comma, Esc,
                    D(0), Lt, F.Id("delta"), Sp, Land, Sp, D(0), Lt, F.Id("kappa"), Sp,
                    Rightarrow, Sp,
                    Operatorname, Grp(F.Id("overlap")),
                    Open, F.Id("delta"), Comma, F.Id("kappa"), Close, Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("min")),
                    Open,
                    Frac, Grp(F.Id("delta")), Grp(F.Id("kappa")), Comma, Sp,
                    Frac, Grp(F.Id("kappa")), Grp(F.Id("delta")),
                    Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For positive real parameters delta and kappa, the formal module writes "
                        + "the two branch vectors explicitly. Before the exceptional point their "
                        + "second coordinates use the real radical sqrt(kappa^2 - delta^2); after "
                        + "it they use i times delta plus or minus sqrt(delta^2 - kappa^2). The "
                        + "overlap is the absolute Hermitian inner product divided by the product "
                        + "of the Euclidean norms.")),
                    Paragraph(Text(
                        "The proof splits at delta <= kappa. In the first phase both squared norms "
                        + "are 2 kappa^2 and the inner-product norm is 2 delta kappa, giving "
                        + "delta/kappa. In the second phase the norm product is 2 delta kappa and "
                        + "the inner-product norm is 2 kappa^2, giving kappa/delta. Positivity "
                        + "then identifies the applicable ratio with their minimum.")),
                    Paragraph(Text(
                        "This node closes only the explicit two-by-two branch-overlap formula in "
                        + "the source theorem. It does not formalize the attached zeta, PT, RH, "
                        + "Lehmer-pair, exceptional-point-sensing, or double-clock "
                        + "interpretations."))),
                DescribeRole.Theorem))));
}
