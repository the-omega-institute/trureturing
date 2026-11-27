using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.Algebra;

internal sealed class FittingDualityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fitting Duality", H("Fitting Duality"),
        Blocks(
            Paragraph(Text("Relative lengths, kernels and determinants over a DVR; functions cut by matrix relations. Elementary bounds for relative lengths of Z_p-submodules: additivity, torsion layers, generators. Fitting ideals: base change, one more relation, iterated along a triangular family. Duality over O/p; dividing by a finite-length submodule costs its length in Fitting ideals.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/Algebra/FittingDuality.exists_cost_le_relLength"),
                H("exists_cost_le_relLength"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let p ≠ 0, pΦ(O^n) ⊆ N, V a module of functions G → O/p. Some K ⊇ N contains Φ(v) whenever all linear Ψ with Ψ∘z ∈ V kill v, and some c ∈ O multiplies Fitt K into Fitt N, v(c) ≤ length of formsMod modulo V.")))))));
}
