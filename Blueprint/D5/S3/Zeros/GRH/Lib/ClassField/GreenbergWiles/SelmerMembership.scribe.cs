using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.ClassField.GreenbergWiles;

internal sealed class SelmerMembershipDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Selmer Membership", H("Selmer Membership"),
        Blocks(
            Paragraph(Text("Membership in Selmer groups of cocycles; dropping conditions and places where unramified.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/ClassField/GreenbergWiles/SelmerMembership.selmerModule_mono"),
                H("selmerModule_mono"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("A member c of the Selmer module for (S, L) lies in that for (T, K) if K ⊆ L and c vanishes on inertia at all places of S outside T.")))))));
}
