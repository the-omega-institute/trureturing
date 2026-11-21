using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.NumericalSemigroup;

internal sealed class IntegerFiberDegreesDocument : IScribeDocumentDefinition
{
    private const string Result = "D5/S3/Combinatorics/NumericalSemigroup/IntegerFiberDegrees.eventual_counts";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The signed degree order and a sufficient cutoff for nonnegative integer fibers.",
        H("Eventual degrees of nonnegative integer fibers"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("eventual-counts"),
                DeclarationHandle.Create(Result),
                H("A positive solution gives consecutive degrees and a sufficient cutoff"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let J be a finite index type and I any index type. Let A be an "
                        + "additive homomorphism from integer-valued functions on J to integer-valued "
                        + "functions on I, and let w be an integer-valued function on I. Assume "
                        + "there is a strictly positive integer vector p on J and a positive natural "
                        + "number B with A(p) = B w.")),
                    Paragraph(Text("Let D consist of the natural numbers N such that A(v) = N w "
                        + "for some nonnegative integer vector v on J. Let h be the additive "
                        + "order of the class of w in the quotient by the range of A.")),
                    Paragraph(Text("The positive solution proves that h is finite. By the quotient "
                        + "equation there is an integer vector u of degree h. Adding enough copies "
                        + "of p to u makes every coordinate nonnegative. This gives two solutions "
                        + "whose degrees differ by h. Their normalized degrees are r and r + 1, "
                        + "where r is a positive multiple of b = B / h. The original positive "
                        + "solution has normalized degree b. Since b and r + 1 are coprime, the "
                        + "bound for two coprime generators gives the cutoff (b − 1) r.")),
                    Paragraph(Text("The finite coordinate set makes a single shift sufficient. "
                        + "Strict positivity lets that shift repair a negative entry at any coordinate. "
                        + "For example, with A(x, y, z) = (2x + y, y + z) and w = (1, 0), "
                        + "the nonnegative vector (1, 0, 0) has degree 2 and the signed vector "
                        + "(0, 1, −1) has degree 1. Every nonnegative vector on the ray has even "
                        + "degree. This example is verified by the two displayed equations.")),
                    Paragraph(Text("The condition B > 0 supplies a positive annihilator of the "
                        + "quotient class. With A = 0 and a singleton target coordinate w = 1, "
                        + "B = 0 gives no finite order for that class."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula h = F.Id("h");
        Formula b = F.Id("b");
        Formula n = F.Id("N");
        Formula r = F.Id("r");
        Formula t = F.Id("t");
        Formula d = F.Id("D");
        return Disp(Seq(
            D(0), Sp, Lt, Sp, h, Sp, Land, Sp,
            Open, Forall, Sp, n, Sp, InMacro, Sp, d, Comma, Sp, h, Sp, Mid, Sp, n, Close,
            Sp, Land, Sp, Exists, Sp, b, Comma, Sp, r, Comma, Sp,
            F.Id("B"), Sp, Eq, Sp, h, b, Sp, Land, Sp, b, Sp, Leq, Sp, r, Sp, Land, Sp,
            D(0), Sp, Lt, Sp, r, Sp, Land, Sp, h, r, Sp, InMacro, Sp, d, Sp, Land, Sp,
            h, Open, r, Plus, D(1), Close, Sp, InMacro, Sp, d, Sp, Land, Sp,
            Open, Forall, Sp, t, Sp, Geq, Sp, Open, b, Minus, D(1), Close, r,
            Comma, Sp, h, t, Sp, InMacro, Sp, d, Close));
    }
}
