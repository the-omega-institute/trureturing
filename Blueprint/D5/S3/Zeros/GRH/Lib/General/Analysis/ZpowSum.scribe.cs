using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.Analysis;

internal sealed class ZpowSumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Zpow Sum", H("Zpow Sum"),
        Blocks(
            Paragraph(Text("General facts on differents, root discriminants; ramified ideals divide the different. One-dimensional Sobolev trace inequality, iterated at a cube corner for families.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/Analysis/ZpowSum.nullstellensatz_exists_le_ker"),
                H("nullstellensatz_exists_le_ker"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Weak Nullstellensatz: a proper ideal J of a finitely generated algebra A over an algebraically closed field k lies in the kernel of some k-algebra homomorphism A → k.")))))));
}
