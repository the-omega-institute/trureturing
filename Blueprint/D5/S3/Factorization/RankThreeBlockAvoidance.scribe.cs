using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization;

internal sealed class RankThreeBlockAvoidanceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Factorization/RankThreeBlockAvoidance.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The distinct-closure incidence counts in the rank-three argument are inconsistent.",
        H("Rank-Three Block Avoidance Counts"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("incidence-count-contradiction"),
                DeclarationHandle.Create(Prefix + "incidence_count_contradiction"),
                H("Two uniform incidence counts cannot coexist"),
                StatementSource.FromAuthor(Formula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "In the distinct-closure branch, b is the size of an original block, "
                    + "m is the number of blocks, and d is the common number of closures "
                    + "through a point. The two counts are b(d-1)=m-1 and "
                    + "(b+m-1)(d-1)=m-1. If b and m are both at least two, subtracting "
                    + "the equations forces (m-1)(d-1)=0; each factor is then handled "
                    + "by the corresponding positivity hypothesis. This is the arithmetic "
                    + "core of the c=1 avoidance step; the matroid and duplicate-closure "
                    + "hypotheses remain outside this module."))),
                DescribeRole.Theorem))));

    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Sub(Formula left, Formula right) =>
        Seq(Open, left, Sp, Minus, Sp, right, Close);

    private static Formula Add(Formula left, Formula right) =>
        Seq(Open, left, Sp, Plus, Sp, right, Close);

    private static Formula Mul(Formula left, Formula right) =>
        Seq(Open, left, Sp, Cdot, Sp, right, Close);

    private static Formula Formula()
    {
        Formula b = F.Id("b");
        Formula m = F.Id("m");
        Formula d = F.Id("d");
        Formula one = D(1);
        Formula blockCount = Sub(Add(b, m), one);
        Formula firstCount = Seq(Mul(b, Sub(d, one)), Sp, Eq, Sp, Sub(m, one));
        Formula secondCount = Seq(Mul(blockCount, Sub(d, one)), Sp, Eq, Sp, Sub(m, one));
        Formula hypotheses = Seq(
            D(2), Sp, Le, Sp, b, Sp, Land, Sp,
            D(2), Sp, Le, Sp, m, Sp, Land, Sp,
            firstCount, Sp, Land, Sp, secondCount);
        return Disp(Seq(
            Forall, Sp, Open, b, Sp, Colon, Sp, Nat(), Close, Sp, Comma, Sp,
            Forall, Sp, Open, m, Sp, Colon, Sp, Nat(), Close, Sp, Comma, Sp,
            Forall, Sp, Open, d, Sp, Colon, Sp, Nat(), Close, Sp, Comma, Sp,
            hypotheses, Sp, Implies, Sp, F.Id("False"), Dot));
    }
}
