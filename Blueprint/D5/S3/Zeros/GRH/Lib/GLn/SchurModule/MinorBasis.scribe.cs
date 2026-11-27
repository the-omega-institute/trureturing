using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.GLn.SchurModule;

internal sealed class MinorBasisDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Minor Basis", H("Minor Basis"),
        Blocks(
            Paragraph(Text("Products of minors form a basis over every ring, with character identity.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/GLn/SchurModule/MinorBasis.exists_minorProduct_basis"),
                H("exists_minorProduct_basis"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For finitely many coloured rows and finitely many columns of colours τ and heights h, there is one family of minor products that, over every commutative ring R, is linearly independent and whose span contains the semi-invariant module of the corresponding weight.")))))));
}
