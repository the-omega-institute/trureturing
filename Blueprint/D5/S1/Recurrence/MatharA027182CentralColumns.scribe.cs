using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class MatharA027182CentralColumnsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/MatharA027182CentralColumns.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The middle columns T(2n,n) and T(2n-1,n-1) of the triangle T(n,k)=t(n,k)-4 satisfy "
            + "one three-term recurrence.",
        H("A shared recurrence for two middle columns"),
        Blocks(
            Node("u", "The central column", "u",
                "u(n) is the integer T(2n,n), where T(n,k)=t(n,k)−4 and "
                + "t(n,k)=C(n+2,k+1)+C(n+1,k)+C(n+1,k+1)+C(n,k). Its first values are "
                + "1, 10, 42, 156, 570, 2096.", DescribeRole.Definition),
            Node("v", "The adjacent column", "v",
                "v(n) is the integer T(2n−1,n−1), read for n≥1; its values from n=1 are "
                + "3, 19, 76, 283, 1046.", DescribeRole.Definition),
            Node("u-rec", "Recurrence for the central column", "u_recurrence",
                "For every n≥2, 2(n+1)u(n)−(7n+5)u(n−1)+2(3−2n)u(n−2)+12(1−3n)=0. "
                + "By Pascal's rule t(n,k)=2C(n+2,k+1)+C(n,k), and this is at least five "
                + "for k≤n, so u(n)=2c(n+1)+c(n)−4 with c(n)=C(2n,n). Substituting, the "
                + "constant terms cancel, and the remaining expression is the combination "
                + "4E(n)+4E(n−1)+E(n−2) of the relations "
                + "E(j): (j+1)c(j+1)=2(2j+1)c(j).", DescribeRole.Theorem),
            Node("v-rec", "Recurrence for the adjacent column", "v_recurrence",
                "For every n≥3, 2(n+1)v(n)−(7n+5)v(n−1)+2(3−2n)v(n−2)+12(1−3n)=0. "
                + "Pascal's rule and the symmetry C(2j+1,j+1)=C(2j+1,j) give "
                + "2C(2j+1,j)=c(j+1), hence 2v(n)=u(n)−4 for n≥1. Twice the left side is "
                + "then the left side of the recurrence for u, because "
                + "2(n+1)−(7n+5)+2(3−2n)=3−9n and 4(3−9n)=12(1−3n).",
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("mathar-a027182-central-columns-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
