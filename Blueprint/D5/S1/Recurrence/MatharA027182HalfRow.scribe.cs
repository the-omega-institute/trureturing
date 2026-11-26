using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class MatharA027182HalfRowDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/MatharA027182HalfRow.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The half-row sums of the triangle T(n,k)=t(n,k)-4 satisfy a seven-term recurrence "
            + "with quadratic coefficients for every n≥6.",
        H("Half-row sums of the A027170 triangle"),
        Blocks(
            Node("b", "Half-row sums", "b",
                "b(n) is the integer sum of T(n,k) over 0≤k≤⌊n/2⌋, where T(n,k)=t(n,k)−4 "
                + "and t(n,k)=C(n+2,k+1)+C(n+1,k)+C(n+1,k+1)+C(n,k). Its first values are "
                + "1, 3, 15, 26, 81, 130, 350, 558.", DescribeRole.Definition),
            Node("rec", "The seven-term recurrence", "half_row_recurrence",
                "Put p0=−(n+2)(3n−20), p1=−(n+1)(3n−11), p2=33n²−180n−100, "
                + "p3=15n²−56n+1, p4=2(−51n²+313n−208), p5=−12(n−1)(n−4) and "
                + "p6=8(9n−11)(n−5). For every n≥6, the sum of pj·b(n−j) over 0≤j≤6 plus "
                + "4(−24n²+196n−365) is zero. Pascal's rule gives T(n,k)=2C(n+2,k+1)+C(n,k)−4. "
                + "The sum of C(2q+1,j) over j≤q is 4^q, and Pascal's rule turns it into "
                + "twice the sum of C(2q,j) over j≤q minus C(2q,q). Hence "
                + "b(2q+1)=9·4^q−4q−6 and 2b(2q)=2·4^(q+1)+2c(q+1)+4^q+c(q)−8q−12 with "
                + "c(q)=C(2q,q). Substituting these into twice the recurrence, the powers of "
                + "four and the polynomial terms cancel, and the central binomial terms "
                + "form an explicit polynomial combination of the relations "
                + "(q+1)c(q+1)=2(2q+1)c(q), separately for even and odd n.",
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("mathar-a027182-half-row-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
