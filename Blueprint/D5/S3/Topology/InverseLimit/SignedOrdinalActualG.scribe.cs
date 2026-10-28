using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.InverseLimit;

internal sealed class SignedOrdinalActualGDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/InverseLimit/SignedOrdinalActualG.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Quantitative oscillation on actual successor spaces", H("One clopen for every signed lift"), Blocks(
            Describe.Lean(DescribeId.Create("clopen"),
                DeclarationHandle.Create(Owner + "clopen"), H("The selected clopen on the successor"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Assume the continuum hypothesis and fix any actual stage a. Let L be the carrier of finalPrefix at nextStage a. The homeomorphism successorHomeomorph sends L to the coordinate carrier of the same selected Result of run a. The clopen B is the inverse image of that Result's quantitativeClopen under this homeomorphism."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("column"),
                DeclarationHandle.Create(Owner + "column"), H("The original fixed natural columns"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The natural index at q is the n field of column q in the same selected Result. Both this sequence and B depend only on the stage and the fixed run, independently of any signed lift sequence."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("column-strict-mono"),
                DeclarationHandle.Create(Owner + "column_strictMono"), H("Strict increase of the fixed columns"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The fixed natural column sequence is strictly increasing, by the original Result's k_mono law."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quantitative-g"),
                DeclarationHandle.Create(Owner + "quantitative_g"), H("Every signed norm-one lift has the fixed parity values"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every actual stage a, let s be any complete sequence of signed measures on L. Assume each s n has total variation one and, for every natural n, its pushforward along the literal restriction from nextStage a to eventRow a equals actualBirth at eventRow a, measured at eta a and n. For every q, even q gives s at column q evaluated on B strictly greater than one sixth; odd q gives exactly zero.")),
                    Paragraph(Text("The selected projection identity on the final limit extends to all of L by projection surjectivity and factorization. Together with selected_measure, this identifies every pushed signed measure with the original selected Q measure, at the unchanged eta. The successor homeomorphism preserves total variation and identifies evaluation on the two clopens. Applying the original quantitative_g therefore gives the estimates on L. No positivity or regularity assumption is needed, so arbitrary regular signed lift sequences are included."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("infinite-values"),
                DeclarationHandle.Create(Owner + "infinite_values"), H("Both requested value sets are infinite"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Under the same all-natural pushforward and norm-one hypotheses, the natural indices n where s n of B is at least one sixth form an infinite set, and the natural indices where s n of B is zero also form an infinite set. The injective images of q under column of twice q and column of twice q plus one lie in these respective sets."))), DescribeRole.Theorem))));
}
