using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.MixedModel;

internal sealed class AdelicSumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adelic Sum", H("Adelic Sum"),
        Blocks(
            Paragraph(Text("Schwartz–Bruhat functions at split places, Schrödinger action, spanned by translates of the lattice indicator. Adelic Heisenberg datum with vacuum splits as real part plus finite part.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/MixedModel/AdelicSum.exists_schrodingerComb_eq"),
                H("exists_schrodingerComb_eq"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If S is disjoint from S̄, every Schwartz–Bruhat function Ψ above S is a finite linear combination of the functions schrodingerAct S y applied to the indicator of the vectors integral on S.")))))));
}
