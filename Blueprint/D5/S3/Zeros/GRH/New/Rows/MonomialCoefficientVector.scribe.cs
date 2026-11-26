using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Rows;

internal sealed class MonomialCoefficientVectorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Monomial Coefficient Vector", H("Monomial Coefficient Vector"),
        Blocks(
            Paragraph(Text("Crude exponential bounds for conjugates of cleared L-values. Integrality and size bounds pass through translation and projection to good types. Integral invariant vector that reads the coefficient of a monomial in given rows.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Rows/MonomialCoefficientVector.exists_int_vector_harmonicPoly_eq"),
                H("exists_int_vector_harmonicPoly_eq"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For a monomial α in rows e of degree dg_τ at each τ, some integral vector has Fock polynomial (∏_τ dg_τ!/α!) times that monomial and is fixed, over any characteristic 0 field, by all g whose columns e are those of 1.")))))));
}
