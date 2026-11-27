using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.LinearAlgebra;

internal sealed class AdelicRingDefsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adelic Ring Defs", H("Adelic Ring Defs"),
        Blocks(
            Paragraph(Text("Generalised inverses, factorisation through a column space, ye + bx = 1 over a field. Linear duality: vectors agreeing under all annihilating functionals agree modulo two subspaces. Integral vectors and matrices over a subring, generalised index, lattices, congruence levels.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/LinearAlgebra/AdelicRingDefs.exists_mulVec_eq_of_annihilator"),
                H("exists_mulVec_eq_of_annihilator"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let s, s' be sets of column indices. If every linear form l killing the columns of P in s and those of P' in s' has l(PX) = l(P'Y), then Px = P'y for some x equal to X off s and y equal to Y off s'.")))))));
}
