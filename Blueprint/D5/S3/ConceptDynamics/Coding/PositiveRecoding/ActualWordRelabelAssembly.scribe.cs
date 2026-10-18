using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.PositiveRecoding;

internal sealed class ActualWordRelabelAssemblyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Assemble actual dictionary weights over typed words.",
        H("Assemble actual dictionary weights over typed words"),
        Blocks(
            Paragraph(Text("path_append_weight proves additivity for dependent finite kernel-ladder paths, including the equality transports in append. dictionary_residue proceeds through the relabel, positive and composition constructors of the original endpoint-typed Word. It uses the actual relabel comparison, both positive-leaf chart corrections and additive concatenation.")),
            Paragraph(Text("The path theorem ranges over Based objects X,Y,Z and arbitrary lengths n,m. The dictionary theorem ranges over every Presentation pair F,H, Word F H and every d with NeZero d and 3 ∣ d. No original-h specialization is introduced and no endpoint correction is erased.")),
            Paragraph(Text("These constructions and identities are repository-derived. Their provenance does not assert literature novelty.")),
            Describe.Lean(DescribeId.Create("positive-recoding-actualwordrelabelassembly-path-append-weight"), DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualWordRelabelAssembly.path_append_weight"), H("path_append_weight"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Weight is additive under actual path concatenation."))), DescribeRole.Theorem),
            Describe.Remark(DescribeId.Create("positive-recoding-actualwordrelabelassembly-dictionary-residue"), DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualWordRelabelAssembly.dictionary_residue"), H("dictionary_residue"), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Actual matrix dictionary weight is the same P1 localized cochain. Both positive-leaf charts and every relabel-leaf phase are retained.")))))));
}
