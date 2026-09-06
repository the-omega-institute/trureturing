using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.PartialIdentification;

internal sealed class QuaternaryResponseTableCodingDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/PartialIdentification/QuaternaryResponseTableCoding.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A Boolean complete response pair is one quaternary symbol. A k-row table is therefore a k-digit radix-four word, while the golden DFAO at index k receives the Zeckendorf representation of the corresponding capacity boundary 4^k.",
        H("Quaternary response-table coding and the golden power input"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("response-pair-digit-equiv"),
                DeclarationHandle.Create(Prefix + "responsePairDigitEquiv"),
                H("Encode one response pair as a base-four digit"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The control bit is the high binary bit and the treatment bit is the low bit. This is a coding equivalence and imposes no response-coordinate independence."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("response-table-digit-equiv"),
                DeclarationHandle.Create(Prefix + "responseTableDigitEquiv"),
                H("Encode a full table coordinatewise"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Mathlib piCongrRight transports the one-row equivalence across all strata."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("response-table-code-equiv"),
                DeclarationHandle.Create(Prefix + "responseTableCodeEquiv"),
                H("Radix-four integer code"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Mathlib finFunctionFinEquiv identifies k quaternary digits with an integer code below four to the k."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("response-table-card-eq-four-pow"),
                DeclarationHandle.Create(Prefix + "responseTable_card_eq_four_pow"),
                H("Exact table-space cardinality"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The unrestricted k-stratum carrier of Boolean complete response pairs has cardinality exactly 4^k."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("response-table-code-lt-capacity"),
                DeclarationHandle.Create(Prefix + "responseTableCode_lt_capacity"),
                H("Codes lie below the capacity boundary"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every actual k-digit table code lies strictly below 4^k. The number 4^k is the one-past-the-last radix capacity, rather than the code of a table."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-base4-power-word-is-response-table-capacity"),
                DeclarationHandle.Create(Prefix + "golden_base4_power_word_is_response_table_capacity"),
                H("The golden DFAO reads the table-space capacity"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The existing golden input base4PowerWord k is the Zeckendorf encoding of 4^k, which is also the exact cardinality of the k-row response-table carrier. This does not identify DFAO state count with causal support size."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-response-prefix"),
                DeclarationHandle.Create(Prefix + "goldenResponsePrefix"),
                H("Embed a golden digit prefix as one response table"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The first k base-four digits of the golden ratio select one distinguished quaternary response table through the standard pair decoder."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("golden-response-prefix-code"),
                DeclarationHandle.Create(Prefix + "goldenResponsePrefixCode"),
                H("Choose one node at each table-tree level"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The distinguished k-row prefix is encoded as one concrete element of Fin(4^k). The coordinate orientation is inherited from Mathlib's explicit radix equivalence."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("golden-response-prefix-digit"),
                DeclarationHandle.Create(Prefix + "goldenResponsePrefix_digit"),
                H("Recover each golden digit"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Re-encoding a row of the distinguished table returns the corresponding existing golden base-four digit."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-response-prefix-cast-succ"),
                DeclarationHandle.Create(Prefix + "goldenResponsePrefix_castSucc"),
                H("Successive prefixes form one nested path"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Passing from k to k+1 preserves every old row. The golden digit sequence therefore selects one path through the rooted four-ary tree whose level k contains all 4^k response tables."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-response-prefix-code-lt-capacity"),
                DeclarationHandle.Create(Prefix + "goldenResponsePrefixCode_lt_capacity"),
                H("The selected node remains inside the full capacity"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The selected level-k node is one of the 4^k possible tables, so its code lies below the same boundary whose Zeckendorf representation is fed to the golden DFAO."))),
                DescribeRole.Theorem))));
}
