using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.ClassField.GreenbergWiles;

internal sealed class SelmerBasicDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Selmer Basic", H("Selmer Basic"),
        Blocks(
            Paragraph(Text("Selmer cocycle groups, their finiteness, S-units, split primes, tame generators, places.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/ClassField/GreenbergWiles/SelmerBasic.finite_unramified_cocycles"),
                H("finite_unramified_cocycles"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For a finite discrete module V of the absolute Galois group of K and a finite set S of primes, there are finitely many continuous 1-cocycles vanishing on all inertia groups above primes outside S.")))))));
}
