using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Cyclotomic.Voronoi;

internal sealed class StickelbergerIntegerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Stickelberger Integer", H("Stickelberger Integer"),
        Blocks(
            Paragraph(Text("Twisted Voronoi congruence, trivial zeros, one bounded integer divisible by all Stickelberger elements.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Cyclotomic/Voronoi/StickelbergerInteger.exists_isStickelbergerBound"),
                H("exists_isStickelbergerBound"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For N, e ≥ 1 there is an integer 1 ≤ X ≤ 2^{(N+e+3)^6} with the property IsStickelbergerBound N e X.")))))));
}
