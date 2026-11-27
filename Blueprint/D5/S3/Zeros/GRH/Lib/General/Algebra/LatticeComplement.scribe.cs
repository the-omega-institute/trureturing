using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.Algebra;

internal sealed class LatticeComplementDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Lattice Complement", H("Lattice Complement"),
        Blocks(
            Paragraph(Text("Integral finite adeles of a CM field with 5040th roots of unity: adelic-ring axioms. Adelic index of a field element equals its absolute norm (product formula). Saturation, indices, discriminant of an orthogonal complement in a unimodular adelic lattice.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/Algebra/LatticeComplement.jacobi_perp_discriminant"),
                H("jacobi_perp_discriminant"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let J be unimodular, F integral, n primitive, FᴴJn = 0 with complementary sizes, N = Gram(F|p) plus c on the p-block, and F left invertible or [det N] ≠ 0. Then n^⊥ ⊆ span F and [det nᴴ(J + c⁻¹JppᴴJ)n]·i²·[c]^|ρ| = [det N], i = [{y | Fy integral} : R^σ].")))))));
}
