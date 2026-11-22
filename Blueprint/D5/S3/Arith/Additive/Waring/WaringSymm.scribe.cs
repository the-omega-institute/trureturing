using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Additive.Waring;

internal sealed class WaringSymmDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pairing opposite integer indices",
        H("Pairing opposite integer indices"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("symm"),
                DeclarationHandle.Create("D5/S3/Arith/Additive/Waring/WaringSymm.sum_Icc_symm_eq"),
                H("Pairing opposite integer indices"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Semigroups/waringformalization2026lean")),
                Blocks(Paragraph(Text("An even function summed from −K through K contributes its value at zero plus twice its sum over the positive indices."))),
                DescribeRole.Theorem)
        )));
}
