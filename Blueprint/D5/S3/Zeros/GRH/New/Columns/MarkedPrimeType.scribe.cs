using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Columns;

internal sealed class MarkedPrimeTypeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Marked Prime Type", H("Marked Prime Type"),
        Blocks(
            Paragraph(Text("Scaled Hecke operator at a marked prime has image of small index on columns.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Columns/MarkedPrimeType.hasType_markOperator"),
                H("hasType_markOperator"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For Λ marked at p, l in Λ and any s, the operator p^{A_l}T_{l,𝔯} (Data.IsMarked.markOperator) keeps the integral columns and is onto modulo p^s up to an index of exponent at most (128A_l log b/(mp) + s/x^14 + x^40)·dim(columns) (HasType).")))))));
}
