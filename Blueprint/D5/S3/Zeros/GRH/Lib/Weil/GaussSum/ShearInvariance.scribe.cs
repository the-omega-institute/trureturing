using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.GaussSum;

internal sealed class ShearInvarianceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Shear Invariance", H("Shear Invariance"),
        Blocks(
            Paragraph(Text("Cut-off ramified character: periodic, of norm one on units, locally constant. The cut-off inverse character is multiplicative on integers. Standard ramified data given by determinants; they are partners and Schwartz-Bruhat. Local Gauss sum from the residue ring; three-block integral frames and standard data. Invariance under block translations implies invariance under shears of standard data.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/GaussSum/ShearInvariance.shear_invariant"),
                H("shear_invariant"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let s be integral, u a column, r a row, su = 0, ru = 0. If the linear form Λ is invariant, on a space M of Schwartz–Bruhat functions, under all y ↦ y + u·z·s·y, it agrees on Ψ_s = stdColDatum and on Ψ_s(y + u·r·y) when both lie in M.")))))));
}
