using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Adelic.CuspForms;

internal sealed class FormRepresentationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Form Representation", H("Form Representation"),
        Blocks(
            Paragraph(Text("Algebraic modular forms: invariant inner product, finite dimension per level.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Adelic/CuspForms/FormRepresentation.finite_formTranslation_levelSpace"),
                H("finite_formTranslation_levelSpace"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For an open subgroup K of the finite adelic points and a character χ of K, the forms of weight κ on a positive definite V on which K acts through χ form a finite-dimensional complex vector space.")))))));
}
