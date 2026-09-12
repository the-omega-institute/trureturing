using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Expansions;

internal sealed class BasePhiNegativePrefixPaddedReadingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Zero padding identifies prefixes 01 and 010, whereas finite-depth occurrences differ exactly at 2, 3, and 4.",
        H("Zero-Padded and Finite-Depth Negative Prefixes"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("padded-prefix-occurs-append-false-iff"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Expansions/BasePhiNegativePrefixPaddedReading.paddedPrefixOccurs_append_false_iff"),
                H("Appending a forced zero preserves padded occurrence"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, Open, F.Id("expansion"), Colon, Sp,
                    Operatorname, Grp(F.Id("BasePhiNegativeExpansion")), Close, Sp,
                    Open, F.Id("w"), Colon, Sp,
                    Operatorname, Grp(F.Id("List")), Sp,
                    Operatorname, Grp(F.Id("Bool")), Close, Sp,
                    Open, F.Id("hw"), Colon, Sp, F.Id("w"), Sp, Neq, Sp,
                    OpenBracket, CloseBracket, Close, Sp,
                    Open, F.Id("hlast"), Colon, Sp,
                    F.Id("w"), Dot, Operatorname, Grp(F.Id("getLast")),
                    Open, F.Id("hw"), Close, Sp, Eq, Sp,
                    Mathrm, Grp(F.Id("true")), Close, Sp,
                    Open, F.Id("N"), Colon, Sp,
                    Operatorname, Grp(F.Id("Nat")), Close, Comma, Esc,
                    Operatorname, Grp(F.Id("PaddedPrefixOccurs")), Open,
                    F.Id("expansion"), Comma, F.Id("w"), Comma, F.Id("N"), Close,
                    Sp, Leftrightarrow, Sp,
                    Operatorname, Grp(F.Id("PaddedPrefixOccurs")), Open,
                    F.Id("expansion"), Comma, F.Id("w"), Sp, Plus, Plus, Sp,
                    OpenBracket, Mathrm, Grp(F.Id("false")), CloseBracket,
                    Comma, F.Id("N"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every expansion and natural number, a nonempty word ending in true occurs "
                    + "in the zero-padded negative tail exactly when the word with false appended occurs. "
                    + "The last-letter hypothesis forces the following digit to be zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("padded-occurrence-set-prefix01-eq-prefix010"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Expansions/BasePhiNegativePrefixPaddedReading.paddedOccurrenceSet_prefix01_eq_prefix010"),
                H("Padded prefixes 01 and 010 have equal occurrence sets"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("paddedOccurrenceSet")), Open,
                    Operatorname, Grp(F.Id("canonicalExpansion")), Comma,
                    OpenBracket, Mathrm, Grp(F.Id("false")), Comma,
                    Mathrm, Grp(F.Id("true")), CloseBracket, Close, Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("paddedOccurrenceSet")), Open,
                    Operatorname, Grp(F.Id("canonicalExpansion")), Comma,
                    OpenBracket, Mathrm, Grp(F.Id("false")), Comma,
                    Mathrm, Grp(F.Id("true")), Comma,
                    Mathrm, Grp(F.Id("false")), CloseBracket, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The canonical zero-padded occurrence sets of 01 and 010 are equal. "
                    + "This establishes only the first equality printed in Proposition 7.8 d) of "
                    + "Dekking's The structure of base phi expansions under the zero-padded reading."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("occurrence-set-prefix01-symm-diff-prefix010"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Expansions/BasePhiNegativePrefixPaddedReading.occurrenceSet_prefix01_symmDiff_prefix010"),
                H("Finite-depth occurrence sets differ exactly at 2, 3, and 4"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("occurrenceSet")), Open,
                    Operatorname, Grp(F.Id("canonicalExpansion")), Comma,
                    OpenBracket, Mathrm, Grp(F.Id("false")), Comma,
                    Mathrm, Grp(F.Id("true")), CloseBracket, Close, Sp, Delta, Sp,
                    Operatorname, Grp(F.Id("occurrenceSet")), Open,
                    Operatorname, Grp(F.Id("canonicalExpansion")), Comma,
                    OpenBracket, Mathrm, Grp(F.Id("false")), Comma,
                    Mathrm, Grp(F.Id("true")), Comma,
                    Mathrm, Grp(F.Id("false")), CloseBracket, Close, Sp, Eq, Sp,
                    OpenBrace, D(2), Comma, D(3), Comma, D(4), CloseBrace))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under the repository's finite-depth reading, the symmetric difference of the "
                    + "canonical occurrence sets of 01 and 010 is exactly the set containing 2, 3, and 4. "
                    + "These are precisely the exceptions to their equality."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Expansions/BasePhiNegativePrefixPaddedReading.result"),
                H("The finite-depth equality claim is false"),
                StatementSource.FromAuthor(Disp(Seq(
                    Neg, Sp, Seq(Left, Open,
                        Operatorname, Grp(F.Id("occurrenceSet")), Open,
                        Operatorname, Grp(F.Id("canonicalExpansion")), Comma,
                        OpenBracket, Mathrm, Grp(F.Id("false")), Comma,
                        Mathrm, Grp(F.Id("true")), CloseBracket, Close, Sp, Eq, Sp,
                        Operatorname, Grp(F.Id("occurrenceSet")), Open,
                        Operatorname, Grp(F.Id("canonicalExpansion")), Comma,
                        OpenBracket, Mathrm, Grp(F.Id("false")), Comma,
                        Mathrm, Grp(F.Id("true")), Comma,
                        Mathrm, Grp(F.Id("false")), CloseBracket, Close,
                        Right, Close)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The finite-depth equality named claim is false; the display unfolds that claim. "
                    + "Thus the first equality in the printed chain holds for the zero-padded reading "
                    + "and fails for the finite-depth reading."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-mem-padded-core010"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Expansions/BasePhiNegativePrefixPaddedReading.two_mem_paddedCore010"),
                H("Two belongs to the padded core of 010"),
                StatementSource.FromAuthor(Disp(Seq(
                    D(2), Sp, InMacro, Sp,
                    Operatorname, Grp(F.Id("PaddedCore")), Open,
                    OpenBracket, Mathrm, Grp(F.Id("false")), Comma,
                    Mathrm, Grp(F.Id("true")), Comma,
                    Mathrm, Grp(F.Id("false")), CloseBracket, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The number 2 is a fiber start whose canonical zero-padded negative tail begins "
                    + "with 010, so it belongs to the padded core of that word."))),
                DescribeRole.Theorem))));
}
