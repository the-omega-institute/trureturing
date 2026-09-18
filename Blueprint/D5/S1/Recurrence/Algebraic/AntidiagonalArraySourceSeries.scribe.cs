using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class AntidiagonalArraySourceSeriesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Algebraic/AntidiagonalArraySourceSeries.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The antidiagonal natural array and the normalized rational source series are uniquely determined, and their first-column coefficients agree after a one-step shift.",
        H("Antidiagonal Array and Source Series"),
        Blocks(
            Paragraph(Text(
                "The array is the total natural function array from the A392095 recurrence: "
                    + "its zeroth row is one and each successor row uses the shifted entry and "
                    + "the finite sum over j from zero through k. The source is the normalized "
                    + "rational power series specified independently by F(x/F(x))=(1-x)^(-1). "
                    + "All coefficients are indexed from zero. The theorem result includes both "
                    + "uniqueness statements, the natural source sequence, and the shifted first-column identity.")),
            Node("array", "The antidiagonal array", "The declaration array is the recursively constructed natural-valued two-index array. "
                + "Its recursion is well founded by the lexicographic measure (n+k,n), with all finite-sum endpoints included.", DescribeRole.Definition),
            Node("IsArray", "The array predicate", "IsArray(T) records the zeroth-row equation and the full successor recurrence for every natural n and k, using the finite range k+1.", DescribeRole.Definition),
            Node("IsSource", "The normalized source predicate", "IsSource(F) requires constant coefficient one and the formal substitution equation F.subst(X times invOfUnit(F,1)) = invOfUnit(1-X,1).", DescribeRole.Definition),
            Node("phi", "The substitution operator", "phi(F) is F.subst(X times invOfUnit(F,1)); it is defined without reference to the array.", DescribeRole.Definition),
            Node("sourceCoeff", "Triangular source coefficients", "sourceCoeff is the recursively defined rational coefficient function obtained by forcing each coefficient of phi to equal the corresponding coefficient of the geometric series.", DescribeRole.Definition),
            Node("sourceSeries", "The independent source series", "sourceSeries is the power series whose coefficient at m is sourceCoeff(m).", DescribeRole.Definition),
            Node("result", "The complete array-source result", "The result proves IsArray(array), uniqueness of every IsArray witness, IsSource(sourceSeries), uniqueness of every normalized source, existence and uniqueness of a natural source sequence, its zero coefficient, coefficient agreement with sourceSeries, and array(n,0)=b(n+1) for every natural n.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role)
    {
        var id = DescribeId.Create("a392095-" + name.ToLowerInvariant());
        var handle = DeclarationHandle.Create(Prefix + name);
        var blocks = Blocks(Paragraph(Text(prose)));
        if (role == DescribeRole.Definition)
        {
            return Describe.Remark(id, handle, H(title), AssessedProvenance.FromRepo(), blocks);
        }

        return Describe.Lean(id, handle, H(title), StatementSource.FromAuthor(Disp(F.Id(name))),
            AssessedProvenance.FromRepo(), blocks, role);
    }
}
