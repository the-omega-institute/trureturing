using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Exchange;

internal sealed class AlgebraicPartDefsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Algebraic Part Defs", H("Algebraic Part Defs"),
        Blocks(
            Paragraph(Text("Weights, Harish-Chandra parameters and ranks of the spaces fit the lift hypotheses. Theta lift of the trivial character of U(1); the splitting carries the Hecke character. Names for the lift of a pair's character, its denominator and normalised norm.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Exchange/AlgebraicPartDefs.hookNumber_eq_prod_factorial"),
                H("hookNumber_eq_prod_factorial"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The hook constant of the weight κ of the auxiliary pair data of X, in rank |n| at every place, equals the product over infinite places τ of (dg τ)!.")))))));
}
