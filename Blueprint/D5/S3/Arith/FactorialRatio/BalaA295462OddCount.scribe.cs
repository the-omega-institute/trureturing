using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FactorialRatio;

internal sealed class BalaA295462OddCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FactorialRatio/BalaA295462OddCount.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The odd values of A295462 below 2^m are counted by c_m=c_{m-1}+c_{m-4}, and their "
            + "indices are enumerated block by block.",
        H("Counting and enumerating the odd values of A295462"),
        Blocks(
            Node("odd", "Odd values", "oddValue",
                "oddValue n states that a(n)=(15n)!(2n)!/((10n)!(6n)!n!) equals an odd "
                + "natural number.", DescribeRole.Definition),
            Node("c", "Counts below powers of two", "c",
                "c m is the number of n with 0≤n<2^m for which a(n) is odd.",
                DescribeRole.Definition),
            Node("u", "Increasing enumeration", "u",
                "u j is the j-th index n, counted from zero, for which a(n) is odd.",
                DescribeRole.Definition),
            Node("count", "The count recurrence", "count_recurrence",
                "c_0=1, c_1=2, c_2=3, c_3=4, and c_m=c_{m−1}+c_{m−4} for every m≥4. Since "
                + "a(n) is odd exactly when any two occupied binary positions of n differ "
                + "by at least four, c counts such n below 2^m. For y<2^e the number 2^e+y "
                + "has the binary positions of y together with e; it is four-separated "
                + "exactly when y is and every position of y is at most e−4, that is "
                + "y<2^(e−3) with truncated subtraction. Splitting the n<2^(e+1) by the "
                + "position e gives c_{e+1}=c_e+c_{e−3} for every e≥0; for e≤2 the second "
                + "term is c_0=1.", DescribeRole.Theorem),
            Node("enum", "Block enumeration", "enumeration",
                "u_0=0, and for every j>0 there is exactly one e with c_e≤j<c_{e+1}; for it, "
                + "u_j=2^e+u_{j−c_e}. Existence and uniqueness follow because c is strictly "
                + "increasing and unbounded with c_0=1. Write i=j−c_e<c_{e−3}; then "
                + "y=u_i<2^(e−3), so 2^e+y is four-separated, and exactly c_e+i such indices "
                + "lie below it. Hence it is the j-th index.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("bala-a295462-odd-count-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
