using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.Algebra;

internal sealed class MultivariateHenselDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Multivariate Hensel", H("Multivariate Hensel"),
        Blocks(
            Paragraph(Text("Multivariable Hensel lemma over an absolutely integrally closed local domain.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/Algebra/MultivariateHensel.multivariate_hensel"),
                H("multivariate_hensel"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Hensel's lemma in several variables: over an absolutely integrally closed local domain A, a system X = p(X) whose right sides vanish modulo the maximal ideal has a solution in A.")))))));
}
