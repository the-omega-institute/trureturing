using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.TwistedHecke;

internal sealed class ClassMeansDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Class Means", H("Class Means"),
        Blocks(
            Paragraph(Text("Integral conjugation-invariant means on generic Levi matrices splitting evaluation at 1 by weight.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/TwistedHecke/ClassMeans.exists_mean"),
                H("exists_mean"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let O be a valuation domain of characteristic 0, the prime p a non-unit, W local, D < p^f, D + k < #residue field of W. For any property P of x-weights, some Levi-conjugation invariant linear form κ on polynomials in a generic matrix kills monomials with row weight ≠ column weight, sends monomials with row weight in P to p^{k²f}·(value at 1) (0 in degree > D), and is a combination of Levi conjugates of forms killing the monomials with row weight outside P.")))))));
}
