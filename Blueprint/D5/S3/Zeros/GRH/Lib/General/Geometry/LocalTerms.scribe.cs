using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.Geometry;

internal sealed class LocalTermsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local Terms", H("Local Terms"),
        Blocks(
            Paragraph(Text("Functor of points on k-algebras; module-valued coefficient functors with scalar action. Global functions on the projective line are constants (polynomials in X and 1/X). Points, tangent polynomial at a coincidence, null local terms, congruence relation, Galois coverings.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/Geometry/LocalTerms.eq_C_of_toLaurent_eq"),
                H("eq_C_of_toLaurent_eq"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If polynomials P, Q over k satisfy P(T) = Q(T⁻¹) as Laurent polynomials, then P and Q are the same constant; this is the statement H⁰(ℙ¹, 𝒪) = k.")))))));
}
