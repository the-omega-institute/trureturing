using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Selmer;

internal sealed class AptTupleDefsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Apt Tuple Defs", H("Apt Tuple Defs"),
        Blocks(
            Paragraph(Text("here (unlike New.Rows, New.Columns, where they are forms) a column is a conjugate self-dual ℓ-adic representation with prescribed jumps, unramified off S and ℓg, and a row is one with S empty whose lattices span all matrices. Also the Selmer length bound and the unit cr_ℓ. Apt labels, idempotents, normalising character, labelled columns, row-plus-string predicate.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Selmer/AptTupleDefs.chiOneInv_spec"),
                H("chiOneInv_spec"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let A lie over w ∤ ℓ and let s⁻¹ act on the residue field of A as the (Nw)^k-th power. Then chiOneInv sends s to ι(ν_w)^{−k}, ν_w the scalar AutChar.frobValue for υ^{r₋} and the rank of W.")))))));
}
