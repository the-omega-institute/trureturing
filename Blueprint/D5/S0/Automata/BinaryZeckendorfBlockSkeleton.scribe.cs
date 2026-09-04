using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Automata;

internal sealed class BinaryZeckendorfBlockSkeletonDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Binary Zeckendorf words admit a first-return block code, and transient typed-DFAO states collapse to output-and-return signatures without increasing state count.",
        H("Binary Zeckendorf First-Return Skeleton"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("binary-zeckendorf-block-code-roundtrip"),
                DeclarationHandle.Create(
                    "D5/S0/Automata/BinaryZeckendorfBlockSkeleton.compressLegalWord_expand"),
                H("The return-block code is uniquely decodable"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Every legal binary Zeckendorf word factors into the first-return blocks 0 and 10, followed by either no terminal symbol or one final 1. Expansion followed by legal-word compression recovers the original code."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("same-transient-signature-same-continuation-behaviour"),
                DeclarationHandle.Create(
                    "D5/S0/Automata/BinaryZeckendorfBlockSkeleton.same_oneSignature_evalFromState"),
                H("A transient signature determines every continuation"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A state over the previous-one base state has no legal one transition. Its current output and optional zero-successor therefore determine its evaluation on every continuation, including undefined continuations."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("canonical-block-skeleton-does-not-increase-state-count"),
                DeclarationHandle.Create(
                    "D5/S0/Automata/BinaryZeckendorfBlockSkeleton.canonical_extract_behavior_and_cardinality"),
                H("Canonical signature reconstruction preserves behaviour and does not add states"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The recurrent fiber is retained verbatim, while one canonical transient state is introduced for each distinct output-and-zero-successor signature used by a recurrent one transition.")),
                    Paragraph(Text(
                        "The reconstructed typed partial DFAO agrees with the original machine on every legal block code. An explicit injection from canonical states into original states proves that canonicalization never increases finite cardinality."))),
                DescribeRole.Theorem)),
        []));
}
