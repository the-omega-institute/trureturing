using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class CrownOrderPolytopeChebyshevDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/lundstrom2025crown");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The weighted auxiliary polynomial is a shifted Chebyshev quotient.",
        H("The crown auxiliary Chebyshev identity"),
        Blocks(
            Paragraph(Text("This polynomial identity is a repository-derived ingredient for the log-concavity argument. It concerns the auxiliary polynomial, not the actual f-polynomial discussed in source Remark 3.8.")),
            Describe.Lean(
                DescribeId.Create("crown-auxiliary-polynomial-chebyshev"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Geometry/CrownOrderPolytopeChebyshev.crownAuxiliaryPolynomial_chebyshev"),
                H("The exact identity for every n"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For every natural n, X times Q_n equals twice T_n((X+2)/2) minus two, as an identity of rational polynomials. Q_n is the sum of A(n,m)X^(m-1) over 1 <= m <= n. The identity is proved through its coefficients and the Chebyshev recurrence, including n equals zero."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Geometry/CrownOrderPolytopeScalar"))
        ]));
}
