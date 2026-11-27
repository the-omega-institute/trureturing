using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.LinearAlgebra;

internal sealed class ColumnLatticesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Column Lattices", H("Column Lattices"),
        Blocks(
            Paragraph(Text("Smith normal form over rings that are valuation rings up to idempotents. Integral and unimodular matrices, congruence subgroups of unitary groups: basic lemmas. Inverse transpose, adjoints of spherical Hecke operators, commutativity by Gelfand's trick. Basic facts on integral lattices, column spans and generalised index over a subring.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/LinearAlgebra/ColumnLattices.liftIntegralFn_mul"),
                H("liftIntegralFn_mul"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For π : R → B, a ∈ GL_n(R), b ∈ GL_m(R) and an m × n matrix M over A, the value of liftIntegralFn π f at bMa equals the value at M of the lift of X ↦ f(π(b)Xπ(a)).")))))));
}
