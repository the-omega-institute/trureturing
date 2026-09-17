using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class PurePrefixResidualLawDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual forbidden prefixes determine an exact rational probability law on the surviving words and an exact probability for every prefix cylinder.",
        H("Exact Laws on Pure-Prefix Survivors"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exact-pure-prefix-residual-law"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Congruence/PurePrefixResidualLaw.exists_exact_residual_law"),
                H("Pruning forbidden descendants gives every residual cylinder probability"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix an alphabet size p >= 3 and any finite height H, "
                        + "including H = 0. At each positive depth through H, "
                        + "choose one forbidden word; the depth-zero entry "
                        + "is ignored. A full word survives exactly when it "
                        + "avoids all of these prefixes. The forbidden choices "
                        + "are arbitrary and may include redundant descendants. "
                        + "The alphabet size need not be prime.")),
                    Paragraph(Text(
                        "Retain the forbidden words that have no shorter "
                        + "forbidden ancestor. Their cylinders are pairwise "
                        + "disjoint and have the same union as all original "
                        + "forbidden cylinders. Consequently the surviving "
                        + "uniform mass Z is exactly one minus the sum of "
                        + "p^(-e) over these retained depths e. The theorem "
                        + "proves Z > 0 and constructs a rational FiniteLaw "
                        + "whose weight is 1 / (p^H * Z) on each surviving "
                        + "word and zero elsewhere.")),
                    Paragraph(Text(
                        "For every test prefix u of depth d, its residual "
                        + "probability is zero if a retained forbidden word "
                        + "is an ancestor of u. Otherwise its probability "
                        + "is (p^(-d) minus the sum of p^(-e) over retained "
                        + "forbidden descendants of u) divided by Z. This "
                        + "formula accounts for the actual overlap geometry "
                        + "rather than assuming that the original forbidden "
                        + "cylinders are disjoint.")),
                    Paragraph(Text(
                        "The constructive geometric step selects the "
                        + "shortest forbidden hit and uses prefix nesting "
                        + "to identify both the full bad set and its "
                        + "intersection with each test cylinder. The proof "
                        + "then directly uses the imported uniform prefix "
                        + "count and probability-conditioning results. This "
                        + "establishes the actual single-coordinate residual "
                        + "law; transport to arithmetic residue coordinates "
                        + "and the full covering application remain separate "
                        + "proof obligations."))),
                DescribeRole.Theorem))));
}
