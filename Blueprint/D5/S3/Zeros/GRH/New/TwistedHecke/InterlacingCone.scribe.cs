using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.TwistedHecke;

internal sealed class InterlacingConeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Interlacing Cone", H("Interlacing Cone"),
        Blocks(
            Paragraph(Text("Cyclic interlacing cone volume as a signed sum over permutations, via determinant of indicators. The cyclic interlacing cone fills the share of one flag in volume.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/TwistedHecke/InterlacingCone.prod_mul_volume_inter_slab"),
                H("prod_mul_volume_inter_slab"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let P > 1, q = P^N, and let Ω be a set such that permStep v P 1 ν lies in Ω exactly when ν lies in pieriCone v P. Then ∏_{l=1}^{k} (q^l − 1)/(q − 1) · vol(Ω ∩ Σ) = vol(Σ), for Σ = slab k D.")))))));
}
