using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.NumberTheory;

internal sealed class ZeroSymmetryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Zero Symmetry", H("Zero Symmetry"),
        Blocks(
            Paragraph(Text("Symmetry of zeros of Dirichlet L-functions from the functional equation, imprimitive characters included.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/NumberTheory/ZeroSymmetry.LFunction_one_sub_eq_zero"),
                H("LFunction_one_sub_eq_zero"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Symmetry of the zeros: if L(s, χ) = 0, re s ≠ 0 and s ≠ 1, then either s is a pole of the gamma factor of χ (where Mathlib gives it the value 0), or L(1 − s, χ⁻¹) = 0.")))))));
}
