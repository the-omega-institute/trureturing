using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Shimura.Uniformisation;

internal sealed class HolomorphicFamilyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Holomorphic Family", H("Holomorphic Family"),
        Blocks(
            Paragraph(Text("Valuation rings of ℂ, holomorphic families of points, jets, uniformisations, theta coordinates. Holomorphic maps into complex points of schemes: criteria, jets, tangent vectors.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Shimura/Uniformisation/HolomorphicFamily.hasSignature_iff"),
                H("hasSignature_iff"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let O act on A = V/L by linear F_a on V and by matrices m_a in dim V coordinates at 0. Some ρ-eigenline of m contains the image of m_b − ρ(c) iff some ρ-eigenline of F contains that of F_b − ρ(c).")))))));
}
