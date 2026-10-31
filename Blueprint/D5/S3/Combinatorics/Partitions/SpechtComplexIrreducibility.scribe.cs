using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class SpechtComplexIrreducibilityDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGroups/tauceti2026spechtpolytabloids");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Specht ComplexIrreducibility",
        H("Specht ComplexIrreducibility"),
        Blocks(
            Paragraph(Text("The intertwining condition is the kernel of the linear map recording commutation defects. Finite free scalar extension identifies the ambient linear-map spaces, and flatness preserves the kernel. The intertwiner dimension survives complexification. Rational scalarity makes the complex endomorphism space one dimensional. The finite-group character norm criterion gives simplicity of the complex scalar extension of the same literal partition-indexed Specht module. Identification of its trace with the three-variable Frobenius coefficient requires a further comparison.")),
            Describe.Lean(DescribeId.Create("isbasechange-basechangehom"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtComplexIrreducibility.isBaseChange_baseChangeHom"),
                H("isBaseChange baseChangeHom"), StatementSource.FromLean(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The statement is the selected structural result for the explicit permutation representation and polytabloid construction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("basechange-apply"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtComplexIrreducibility.baseChange_apply"),
                H("baseChange apply"), StatementSource.FromLean(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The statement is the selected structural result for the explicit permutation representation and polytabloid construction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("intertwiningmapbasechangeequiv"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtComplexIrreducibility.intertwiningMapBaseChangeEquiv"),
                H("intertwiningMapBaseChangeEquiv"), StatementSource.FromLean(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The statement is the selected structural result for the explicit permutation representation and polytabloid construction."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("finrank-intertwiningmap-basechange"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtComplexIrreducibility.finrank_intertwiningMap_baseChange"),
                H("finrank intertwiningMap baseChange"), StatementSource.FromLean(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The statement is the selected structural result for the explicit permutation representation and polytabloid construction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("spechtmodulec-def"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtComplexIrreducibility.spechtModuleℂ_def"),
                H("spechtModuleℂ def"), StatementSource.FromLean(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The statement is the selected structural result for the explicit permutation representation and polytabloid construction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("instsimplespechtmodulec"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtComplexIrreducibility.instSimpleSpechtModuleℂ"),
                H("instSimpleSpechtModuleℂ"), StatementSource.FromLean(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The statement is the selected structural result for the explicit permutation representation and polytabloid construction."))),
                DescribeRole.Theorem))));
}
