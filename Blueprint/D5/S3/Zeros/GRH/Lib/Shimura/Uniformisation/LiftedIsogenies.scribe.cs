using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Shimura.Uniformisation;

internal sealed class LiftedIsogeniesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Lifted Isogenies", H("Lifted Isogenies"),
        Blocks(
            Paragraph(Text("Every full complex PEL abelian variety is uniformised by a frame and reflection. Polarisation kernel has no p-part; maps respecting level and pairing are identity. Lifts of multiplications are isogenies that keep the pairing; division of lifts.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Shimura/Uniformisation/LiftedIsogenies.exists_lift_of_kills_ker"),
                H("exists_lift_of_kills_ker"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Division of lifts. Let f: A_x → A_x' and F: A_x → A_x₁ be homomorphisms of deformations over k[ε] reducing to a ≠ 0 and ca. If F kills all points over finite local k[ε]-algebras killed by f and a², some homomorphism A_x' → A_x₁ reduces to c.")))))));
}
