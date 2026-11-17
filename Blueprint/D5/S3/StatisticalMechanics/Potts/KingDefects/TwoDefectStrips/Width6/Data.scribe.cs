using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6;
internal sealed class DataDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/SpinModels/hardin2013a229753");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite data support the literal width-six king-grid recurrence.", H("Two-defect king transfers"),
        Blocks(
            Describe.Remark(DescribeId.Create("row"),
                DeclarationHandle.Create(Prefix + "Row"), H("Row"),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The Lean type is Fin 6 -> Fin 4. Rows carry the four labelled colours on six ordered columns.")))),
            Describe.Remark(DescribeId.Create("horizontal"),
                DeclarationHandle.Create(Prefix + "horizontal"), H("horizontal"),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The Lean type is Finset (Fin 6 x Fin 6). The five ordered bonds join consecutive columns. This consumed alias delegates to StripDefects.HardinA229584StripData.horizontal. It is bind-only.")))),
            Describe.Remark(DescribeId.Create("between"),
                DeclarationHandle.Create(Prefix + "between"), H("between"),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The Lean type is Finset (Fin 6 x Fin 6). The sixteen ordered bonds comprise six vertical, five diagonal and five antidiagonal bonds.")))),
            Describe.Remark(DescribeId.Create("valid"),
                DeclarationHandle.Create(Prefix + "Valid"), H("Valid"),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The Lean type is Row -> Nat -> Prop. A residual budget d is valid when d <= 2 and the current row has at most 2-d horizontal defects.")))),
            Describe.Remark(DescribeId.Create("cl"),
                DeclarationHandle.Create(Prefix + "cl"), H("cl"),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The Lean type is Row -> Nat -> Fin 96. The classifier depends only on the row equality pattern and d mod 3, and has 96 values. The class certificates pin every valid canonical source row; colour relabelling extends the result to all rows.")))),
            Describe.Remark(DescribeId.Create("proper-successors"),
                DeclarationHandle.Create(Prefix + "properSuccessors"), H("Proper zero-budget successors"),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The Lean type is Row -> List (Fin 96). Map the original width-six owner's allowed xor shifts through the existing class map and sort. Each allowed shift contributes exactly one labelled successor.")))),
            Describe.Remark(DescribeId.Create("t"),
                DeclarationHandle.Create(Prefix + "T"), H("T"),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The Lean type is Matrix (Fin 96) (Fin 96) Int. This is a 96 by 96 integer matrix. Proper zero-budget rows count properSuccessors at representative rows; all other rows retain their exact defect data. Certificate.transition_counts pins every entry as the exact sum over labelled next rows.")))),
            Describe.Remark(DescribeId.Create("initial"),
                DeclarationHandle.Create(Prefix + "initial"), H("initial"),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The Lean type is Fin 96 -> Int. Forward.structural_certificate pins its entries by summing first rows with at most two horizontal defects.")))),
            Describe.Remark(DescribeId.Create("terminal"),
                DeclarationHandle.Create(Prefix + "terminal"), H("terminal"),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The Lean type is Fin 96 -> Int. Forward.structural_certificate pins the terminal value as the indicator that the residual budget is zero.")))),
            Describe.Remark(DescribeId.Create("w"),
                DeclarationHandle.Create(Prefix + "W"), H("W"),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The Lean type is Fin 12 -> Fin 96 -> Int. The table has twelve rows and 96 columns. Forward.structural_certificate pins W(0), eleven forward steps and the six-term relation at W(11).")))),
            Describe.Remark(DescribeId.Create("classlist"),
                DeclarationHandle.Create(Prefix + "classList"), H("classList"),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The Lean type is Fin 96 -> List (Fin 96). Certificate.class_counts pins the multiplicity of each class as the corresponding matrix entry. These finite lists describe all successor multiplicities without transcribing the matrix.")))),
            Describe.Remark(DescribeId.Create("successors"),
                DeclarationHandle.Create(Prefix + "successors"), H("successors"),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The Lean type is Row -> Nat -> List (Fin 96). For a horizontally proper source at zero budget use properSuccessors. Otherwise enumerate every labelled next row, retain those within budget, map to its residual-budget class and sort; TableBridge.count_successors identifies each multiplicity with the transfer sum.")))))));

}
