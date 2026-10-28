using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.CubicGain;

internal sealed class LiteralSylvesterBoundsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact parameter degrees of the original fixed elimination determinants",
        H("Fixed row and column orders"),
        Blocks(
            Paragraph(Text("The coefficient ring is Z[b] and the outer polynomial variable is the original independent r. sourcePolynomial has entries E01, E02 and E12, in that order. For k:Fin 2, sylvesterRow consists of r^14 E01 through E01 followed by r^14 E(k+1) through E(k+1). literalSylvester retains these thirty rows in columns r^29 through 1. actualResultant(k) is exactly its determinant, so k=0 denotes the source R1 and k=1 denotes R2.")),
            Paragraph(Text("Every source coefficient of r^j has b degree at most 17-j when nonzero. A row shifted by s and a column of exponent c therefore have nonzero entry degree plus c at most 17+s. Every nonzero permutation product uses every column once. Summing these inequalities gives the degree bound for each determinant term and hence the determinant. Zero entries and zero determinant terms are included.")),
            Describe.Lean(DescribeId.Create("literal-sylvester-degree-bound"),
                DeclarationHandle.Create("D5/S3/Observer/CubicGain/LiteralSylvesterBounds.literal_resultant_degree_bound"),
                H("Both original fixed resultants have degree at most 285"),
                StatementSource.FromAuthor(ResultantBound()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every k:Fin 2, actualResultant(k) has natural degree at most 285. The row weights are 17 plus shifts 14 through 0, twice; the column weights are 29 through 0. No assumption requires a leading coefficient to remain nonzero at any parameter value."))), DescribeRole.Theorem),
            Paragraph(Text("The original fixed linear minors are actualMinorA0 and actualMinorC0 of ActualMinorLift. They retain rows r^13 E01 through E01 followed by r^13 E02 through E02. Their first twenty-seven columns are r^28 through r^2; their final columns are respectively r and 1, with no sign or scale adjustment.")),
            Describe.Lean(DescribeId.Create("literal-linear-minor-degree-bounds"),
                DeclarationHandle.Create("D5/S3/Observer/CubicGain/LiteralSylvesterBounds.literal_minor_degree_bounds"),
                H("The original fixed linear-minor degree bounds"),
                StatementSource.FromAuthor(MinorBounds()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The natural degrees of actualMinorA0 and actualMinorC0 are at most 252 and 253 respectively. The same weighted argument uses shifts 13 through 0 twice and the original retained column exponents."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("literal-elimination-exact-degrees"),
                DeclarationHandle.Create("D5/S3/Observer/CubicGain/LiteralSylvesterBounds.literal_elimination_exact_degrees"),
                H("Exact degrees of the original fixed determinants"),
                StatementSource.FromAuthor(ExactDegrees()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Both original fixed Sylvester determinants have natural degree 285; the original r-column and constant-column minors have natural degrees 252 and 253 respectively. For each entry the proof extracts the coefficient at row weight minus column exponent. Scaling rows and columns by powers of X identifies the determinant coefficient with the determinant of this integer leading matrix. The exact full-matrix certificates in LiteralLeadingCertificates prove that all four leading determinants are nonzero. Every coefficient array is checked against sourcePolynomial, and every matrix entry is connected to the original fixed rows and columns."))), DescribeRole.Theorem),
            Paragraph(Text("These are polynomial bounds and exact degrees before specialization. All rows, columns and zero padding remain fixed even when specialization lowers a leading degree. These results do not prove exact resultant or minor factorizations, the displayed common factors, primitive positive normalization, coprimality, or any root or world exhaustion.")))));

    private static Formula Call(string name, params Formula[] args) =>
        Seq(Operatorname, Grp(F.Id(name)), Open, Seq(args), Close);
    private static Formula ResultantBound() => Disp(Seq(
        Forall, Sp, F.Id("k"), InMacro, Sp, Call("Fin", D(2)), Comma, Sp,
        Call("natDegree", Call("actualResultant", F.Id("k"))), Leq, Sp, D(2,8,5)));
    private static Formula ExactDegrees() => Disp(Seq(
        Open, Forall, Sp, F.Id("k"), InMacro, Sp, Call("Fin", D(2)), Comma, Sp,
        Call("natDegree", Call("actualResultant", F.Id("k"))), Eq, Sp, D(2,8,5), Close,
        Land, Sp, Call("natDegree", Seq(F.Id("a"), Underscore, Grp(D(0)))), Eq, Sp, D(2,5,2),
        Land, Sp, Call("natDegree", Seq(F.Id("c"), Underscore, Grp(D(0)))), Eq, Sp, D(2,5,3)));
    private static Formula MinorBounds() => Disp(Seq(
        Call("natDegree", Seq(F.Id("a"), Underscore, Grp(D(0)))), Leq, Sp, D(2,5,2), Land, Sp,
        Call("natDegree", Seq(F.Id("c"), Underscore, Grp(D(0)))), Leq, Sp, D(2,5,3)));
}
