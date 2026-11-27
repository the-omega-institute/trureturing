using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Adelic.Adeles;

internal sealed class AdeleSelfDualDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adele Self Dual", H("Adele Self Dual"),
        Blocks(
            Paragraph(Text("Rational scalars and matrices are their own annihilators in the adeles.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Adelic/Adeles/AdeleSelfDual.isDualFamily_ratAdeles"),
                H("isDualFamily_ratAdeles"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Self-duality of the adeles (Tate): a ↦ (x ↦ ψ(ax)) is an injective homomorphism from E to continuous unitary characters of the adeles trivial on E, and the common kernel lies in E.")))))));
}
