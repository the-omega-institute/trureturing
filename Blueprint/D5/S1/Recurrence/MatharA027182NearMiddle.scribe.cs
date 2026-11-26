using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class MatharA027182NearMiddleDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/MatharA027182NearMiddle.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The near-middle column T(2n,n-2) of the triangle T(n,k)=t(n,k)-4 satisfies a "
            + "three-term recurrence with quadratic coefficients for every n≥4.",
        H("A recurrence for the near-middle column"),
        Blocks(
            Node("z", "The near-middle column", "z",
                "z(n) is the integer T(2n,n−2), where T(n,k)=t(n,k)−4 and "
                + "t(n,k)=C(n+2,k+1)+C(n+1,k)+C(n+1,k+1)+C(n,k); it is read for n≥2, "
                + "with first values 9, 58, 264, 1106, 4495.", DescribeRole.Definition),
            Node("rec", "The three-term recurrence", "z_recurrence",
                "For every n≥4, −2(n+3)(139n−175)z(n)+(1279n²+1334n−1089)z(n−1)"
                + "−2(167n+121)(2n−3)z(n−2)+12(111n²+456n+229)=0. With B(j)=C(2j,j−2), "
                + "Pascal's rule gives z(j)=2B(j+1)+B(j)−4 for j≥2, and the factorial "
                + "formula gives E(j): (j−1)(j+3)B(j+1)=2(j+1)(2j+1)B(j). Multiplying the "
                + "left side by n−1 turns it into (167n+121)E(n−2)+8(7n−79)E(n−1)"
                + "−4(139n−175)E(n), with every relation written as left minus right; "
                + "the constant terms cancel. Since n−1≠0, the left side vanishes.",
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("mathar-a027182-near-middle-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
