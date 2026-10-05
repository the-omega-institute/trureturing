using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Experiment;

internal sealed class PositiveRankOneSecantsDocument : IScribeDocumentDefinition
{
    private static Formula Matrix(Formula p, Formula q, Formula r, Formula s) =>
        Seq(Begin, Grp(F.Id("pmatrix")), p, Amp, q, RowBreak, r, Amp, s,
            End, Grp(F.Id("pmatrix")));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact secant directions of strictly positive real rank-one matrices.",
        H("Positive Rank-One Secants"),
        Blocks(
            Paragraph(Text(
                "Source is the set of real 2 by 2 matrices R with every entry "
                + "strictly positive and R11 R22 = R12 R21. These are precisely "
                + "the strictly positive rank-one relation matrices. The diagonal "
                + "entries of a traceless difference are a and -a.")),
            Describe.Lean(DescribeId.Create("positive-rank-one-secant-criterion"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Experiment/PositiveRankOneSecants.result"),
                H("The complete traceless secant criterion"),
                StatementSource.FromAuthor(Criterion()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The nonzero hypothesis excludes coincident endpoints. "
                        + "No condition on the determinant of the difference is imposed. "
                        + "Since the difference is traceless, the two endpoints have "
                        + "equal trace; since the difference is nonzero, they are distinct.")),
                    Paragraph(Text(
                        "For necessity when a = 0, the diagonal entries agree. The "
                        + "rank-one equations then equate the products of the two "
                        + "offdiagonal entries. Subtracting those products gives "
                        + "b times the second endpoint's lower-left entry plus c times "
                        + "the first endpoint's upper-right entry equal to zero. "
                        + "Positivity and the nonzero difference force b and c to "
                        + "have opposite signs.")),
                    Paragraph(Text(
                        "For a nonzero diagonal choose L = 1 + abs(b) + abs(c), "
                        + "T = (a squared + bc + (b+c)L)/a, and "
                        + "H = sqrt(T squared + 4L squared). Put p = (H-T)/2 and "
                        + "s = (H+T)/2. Then p and s are positive, ps = L squared, "
                        + "and s-p = T. The endpoints have rows (p,L),(L,s) and "
                        + "(p+a,L+b),(L+c,s-a). The second rank-one equation and "
                        + "the sign of a ensure that both its diagonal entries are positive.")),
                    Paragraph(Text(
                        "For a = 0 and b > 0 > c, put d = sqrt(-2bc). "
                        + "The endpoints have rows (d,b),(-2c,d) and (d,2b),(-c,d). "
                        + "Their entries are positive, both offdiagonal products equal "
                        + "d squared, and their difference is the required matrix. "
                        + "For b < 0 < c apply this construction to the negative "
                        + "difference and exchange the endpoints."))),
                DescribeRole.Theorem))));

    private static Formula Criterion()
    {
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula c = F.Id("c");
        Formula difference = Matrix(a, b, c, Seq(Minus, a));
        Formula first = Seq(F.Id("R"), Underscore, Grp(D(0)));
        Formula second = Seq(F.Id("R"), Underscore, Grp(D(1)));
        return Disp(Seq(
            Forall, Sp, a, Comma, b, Comma, c, Colon, Sp, Mathbb, Grp(F.Id("R")),
            Comma, Sp, difference, Sp, Neq, Sp, D(0), Sp, Implies, Sp, Open,
            Open, Exists, Sp, first, Comma, second, Colon, Sp,
            Operatorname, Grp(F.Id("Source")), Comma, Sp,
            difference, Sp, Eq, Sp, second, Minus, first, Close,
            Sp, Iff, Sp, Open, a, Sp, Neq, Sp, D(0), Sp, Lor, Sp,
            b, c, Sp, Lt, Sp, D(0), Close, Close));
    }
}
