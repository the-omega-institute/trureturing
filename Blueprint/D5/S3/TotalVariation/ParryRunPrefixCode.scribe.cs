using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class ParryRunPrefixCodeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prefix freedom of the actual Parry run words at each fixed run count.",
        H("Unique parsing of complete Parry runs"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("run-word-prefix"),
                DeclarationHandle.Create(
                    "D5/S3/TotalVariation/ParryRunPrefixCode.run_word_prefix_iff"),
                H("Prefix-free run words"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Take two lists of zero-run and one-run lengths with the same number "
                        + "of pairs. Every length is at least one, with no upper bound. "
                        + "Prepend the boundary bits true, false to the existing runContinuation "
                        + "of each list. One resulting word is a prefix of the other exactly "
                        + "when the two lists of pairs are equal. The total bit lengths need "
                        + "not be assumed equal.")),
                    Paragraph(Text(
                        "The boundary already contains the first zero of the first run. "
                        + "A pair with lengths z and o therefore adds z minus one zeros, "
                        + "then o ones, then the first zero of the next run. After removing "
                        + "the common boundary, the first true bit determines z minus one. "
                        + "Canceling those zeros, the first false bit determines o. "
                        + "Canceling the ones and their closing zero leaves the same prefix "
                        + "comparison for the remaining pairs. Induction on the common run "
                        + "count finishes the parsing. At count zero both lists are empty; "
                        + "at count one the two forced switches determine the only pair.")),
                    Paragraph(Text(
                        "This is the deterministic prefix-free run-word prerequisite for "
                        + "summing disjoint actual prefix cylinders, and, after reversal, "
                        + "suffix cylinders at the same run count. It introduces no probability "
                        + "law, independence assumption, or containment condition. The full "
                        + "original shared-rule error bound of 512 divided by R remains open."))),
                DescribeRole.Theorem))));
}
