using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.ClassField.HeckeL;

internal sealed class HeckeContinuationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hecke Continuation", H("Hecke Continuation"),
        Blocks(
            Paragraph(Text("Hecke's theorem: L-function of a nontrivial Hecke character is analytic at 1.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/ClassField/HeckeL/HeckeContinuation.eulerProd_ne_zero"),
                H("eulerProd_ne_zero"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For a Hecke character ψ of a number field with ψ² ≠ 1 and a finite set S of primes, the partial L-function L^S(s, ψ) does not vanish at any real s ≥ 1.")))))));
}
