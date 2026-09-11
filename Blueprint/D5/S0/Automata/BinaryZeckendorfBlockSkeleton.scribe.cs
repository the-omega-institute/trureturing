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
                DescribeId.Create("canonical-block-skeleton-does-not-increase-state-count"),
                DeclarationHandle.Create(
                    "D5/S0/Automata/BinaryZeckendorfBlockSkeleton.canonical_extract_behavior_and_cardinality"),
                H("Canonical signature reconstruction preserves behaviour and does not add states"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The recurrent fiber is retained verbatim, while one canonical transient state is introduced for each distinct output-and-zero-successor signature used by a recurrent one transition.")),
                    Paragraph(Text(
                        "The reconstructed typed partial DFAO agrees with the original machine on every legal block code. An explicit injection from canonical states into original states proves that canonicalization never increases finite cardinality."))),
                DescribeRole.Theorem)),
        []));
}
