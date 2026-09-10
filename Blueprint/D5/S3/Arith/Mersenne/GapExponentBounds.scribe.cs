using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Mersenne;

internal sealed class GapExponentBoundsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/zizka2025a390871");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The binary exponent interval for square differences of Mersenne form.",
        H("The exponent conjecture of A390871"),
        Blocks(Describe.Lean(
            DescribeId.Create("mersenne-gap-exponent-bounds"),
            DeclarationHandle.Create(
                "D5/S3/Arith/Mersenne/GapExponentBounds.mersenne_gap_exponent_bounds"),
            H("Both exponent bounds"),
            StatementSource.FromAuthor(BoundsFormula()),
            AssessedProvenance.FromRepo(Source),
            Blocks(
                Paragraph(Text(
                    "All variables range over natural numbers. The integer t is the floor "
                    + "of the base-two logarithm of k. The OEIS entry explicitly conjectures "
                    + "this exponent interval. Israel's comments there prove the divisibility "
                    + "observation and a factor construction.")),
                Paragraph(Text(
                    "Exponent zero is impossible when r is smaller than k. A difference "
                    + "k minus r of one forces k to be a power of two. A difference of two "
                    + "contradicts parity. Therefore r plus three is at most k. Comparing "
                    + "r squared with k minus three squared gives six times k at most "
                    + "two to the m plus eight.")),
                Paragraph(Text(
                    "Write p as two to the t. The integer logarithm gives p at most k "
                    + "and k smaller than twice p. The first inequality and the gap estimate "
                    + "give four times p smaller than two to the m. The second gives "
                    + "k squared plus one smaller than two to the power two t plus two. "
                    + "Strict monotonicity of powers yields both bounds. The proof includes "
                    + "r equal to zero and retains the defining restriction m at most k. "
                    + "The solution k=12, r=9, m=6 attains the lower bound."))),
            DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula LogK() => Seq(Lfloor, Log, Underscore, D(2), Sp, V("k"), Rfloor);
    private static Formula BoundsFormula() => Disp(Seq(
        Forall, Sp, V("k"), Comma, V("r"), Comma, V("m"), InMacro, Mathbb, Grp(V("N")),
        Comma, Sp, Open,
        D(8), Lt, V("k"), Sp, Land, Sp,
        Open, Forall, Sp, V("u"), InMacro, Mathbb, Grp(V("N")), Comma, Sp,
        V("k"), Sp, Neq, Sp, Pow(D(2), V("u")), Close, Sp, Land, Sp,
        V("r"), Lt, V("k"), Sp, Land, Sp, V("m"), Sp, Le, Sp, V("k"), Sp, Land, Sp,
        Pow(V("k"), D(2)), Plus, D(1), Eq, Pow(V("r"), D(2)), Plus, Pow(D(2), V("m")),
        Close, Sp, Implies, Sp,
        LogK(), Plus, D(3), Sp, Le, Sp, V("m"), Sp, Land, Sp,
        V("m"), Sp, Le, Sp, D(2), LogK(), Plus, D(1)));
}
