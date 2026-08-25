using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.ErrorExponents;

internal sealed class ChernoffInformationZeroCriterionDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Chernoff information vanishes exactly when two finite probability laws agree.",
        H("Chernoff Information Zero Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("same-law-iff-chernoff-information-zero"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/ErrorExponents/ChernoffInformationZeroCriterion."
                        + "same_law_iff_chernoff_information_zero"),
                H("Same law iff Chernoff information is zero"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The optimized coefficient is the infimum, over lambda in the closed "
                            + "unit interval, of the finite sum of p(i)^lambda times "
                            + "q(i)^(1-lambda). Chernoff information is its negative extended-real "
                            + "logarithm, so a zero coefficient has infinite information rather "
                            + "than being collapsed by the totalized real logarithm at zero.")),
                    Paragraph(Text(
                        "At lambda one half, the coefficient is the repository's canonical "
                            + "Bhattacharyya affinity. If the optimized coefficient is one, this "
                            + "half-parameter slice is forced to be one; the frozen complementary "
                            + "square bound then forces total variation to vanish and hence the "
                            + "two laws to agree.")),
                    Paragraph(Text(
                        "The second public clause records the source consequence: a strictly "
                            + "positive exponent certifies a genuine difference between the laws, "
                            + "independently of how many repeated samples are later taken."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var content = new List<Formula>
        {
            Operatorname, Grp(F.Id(name)), Open
        };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                content.Add(Comma);
                content.Add(Sp);
            }
            content.Add(arguments[index]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }

    private static Formula TheoremFormula()
    {
        Formula alphabet = Iota;
        Formula first = F.Id("P");
        Formula second = F.Id("Q");
        Formula index = F.Id("i");
        Formula firstAt = Call("P", index);
        Formula secondAt = Call("Q", index);
        Formula information = Call("ChernoffInformation", first, second);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, alphabet, Esc,
            OpenBracket, Call("Fintype", alphabet), CloseBracket, Comma, RowBreak, Grp(),
            Forall, Sp, first, Comma, Sp, second, Colon, Sp,
            alphabet, Sp, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak, Grp(),
            Open,
            Open, Forall, Sp, index, Comma, Sp, D(0), Sp, Le, Sp, firstAt, Close,
            Sp, Land, Sp,
            Sum, Underscore, Grp(index), Sp, firstAt, Sp, Eq, Sp, D(1), Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, index, Comma, Sp, D(0), Sp, Le, Sp, secondAt, Close,
            Sp, Land, Sp,
            Sum, Underscore, Grp(index), Sp, secondAt, Sp, Eq, Sp, D(1),
            Close, Sp, Rightarrow, RowBreak, Grp(),
            OpenBracket,
            Open, first, Sp, Eq, Sp, second, Sp, Iff, Sp,
            information, Sp, Eq, Sp, D(0), Close,
            Sp, Land, RowBreak, Grp(),
            Open, D(0), Sp, Lt, Sp, information, Sp, Rightarrow, Sp,
            first, Sp, Neq, Sp, second, Close,
            CloseBracket, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
