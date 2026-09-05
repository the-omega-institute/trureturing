using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Chronology;

internal sealed class BinaryParikhStepTwoBridgeDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/Chronology/BinaryParikhStepTwoBridge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A standard binary Parikh matrix realizes letter counts and scattered pairs as existing Chen and Magnus coordinates.",
        H("Binary Parikh, Chen, and Magnus Coordinates"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("binary-parikh-matrix-entries"),
                DeclarationHandle.Create(Prefix + "binary_parikh_matrix_entries"),
                H("Literal ordered matrix transport"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The two superdiagonal entries count true and false letters. The upper-right entry counts scattered true-before-false pairs, including pairs separated by other letters."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("binary-parikh-magnus-center"),
                DeclarationHandle.Create(Prefix + "binary_doubled_magnus_center"),
                H("Exact centered second-order coordinate"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The existing doubled Magnus coordinate has center 2c-rf. Here r and f are the two letter counts and c is the ordered-pair count. The same c occurs in the factorial Chen coordinate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("binary-parikh-unrestricted-collision"),
                DeclarationHandle.Create(Prefix + "binary_parikh_arbitrary_word_collision"),
                H("Explicit unrestricted collision"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "ABBA and BAAB have the same binary Parikh matrix although their words differ. Faithfulness requires a language restriction."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "Classical anchor: Mateescu, A. Salomaa, K. Salomaa and Yu, A sharpening of the Parikh mapping, RAIRO ITA 35(6), 2001, 551-564. DOI 10.1051/ita:2001131. This module integrates the classical representation with existing repository signatures; it does not claim a new Parikh mapping.")))));
}
