using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.Measure;

internal sealed class SubgroupIntegralDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Subgroup Integral", H("Subgroup Integral"),
        Blocks(
            Paragraph(Text("Quotient measure defined by a cutoff weight of mass one on each orbit. Haar integrals over subgroups: translation, character orthogonality, sums over finite quotients.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/Measure/SubgroupIntegral.setIntegral_char"),
                H("setIntegral_char"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Orthogonality of characters: let ν be a translation-invariant Borel measure on V, M an open subgroup, and χ(x+y) = χ(x)χ(y) for all x, y in V. Then ∫_M χ dν is ν(M) (read as 0 if infinite) if χ = 1 on M, and 0 otherwise.")))))));
}
