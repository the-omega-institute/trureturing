using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Automata;

internal sealed class BinaryZeckendorfBlockSkeletonCoreDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Binary Zeckendorf return-block codes are uniquely decodable, and transient typed-DFAO signatures determine every continuation.",
        H("Binary Zeckendorf Block Codes and Transient Signatures"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("binary-zeckendorf-block-code-roundtrip"),
                DeclarationHandle.Create(
                    "D5/S0/Automata/BinaryZeckendorfBlockSkeletonCore.compressLegalWord_expand"),
                H("The return-block code is uniquely decodable"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Every legal binary Zeckendorf word factors into the first-return blocks 0 and 10, followed by either no terminal symbol or one final 1. Expansion followed by legal-word compression recovers the original code."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("same-transient-signature-same-continuation-behaviour"),
                DeclarationHandle.Create(
                    "D5/S0/Automata/BinaryZeckendorfBlockSkeletonCore.same_oneSignature_evalFromState"),
                H("A transient signature determines every continuation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A state over the previous-one base state has no legal one transition. Its current output and optional zero-successor therefore determine its evaluation on every continuation, including undefined continuations."))),
                DescribeRole.Theorem)),
        []));
}
