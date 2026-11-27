using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.NumberTheory;

internal sealed class ValuationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Valuation", H("Valuation"),
        Blocks(
            Paragraph(Text("Inertia at p fixes roots of unity of order prime to p. l-adic valuation on the algebraic closure; normalised lengths over integer rings.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/NumberTheory/Valuation.normLength"),
                H("normLength"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Normalised length: the additive map sending n to n·v(ϖ), ϖ a uniformiser of O and v(ℓ) = 1, so that O mod ℓ has length 1.")))))));
}
