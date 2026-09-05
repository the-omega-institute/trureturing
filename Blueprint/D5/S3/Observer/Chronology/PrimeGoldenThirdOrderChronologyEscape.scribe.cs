using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Chronology;

internal sealed class PrimeGoldenThirdOrderChronologyEscapeDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/Chronology/PrimeGoldenThirdOrderChronologyEscape.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two prime-golden words can share bidegree, complete scalar trajectory, and the full step-two signature while a cubic ordered moment separates their chronology.",
        H("Prime-Golden Third-Order Chronology Escape"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-golden-third-order-chronology-escape"),
                DeclarationHandle.Create(
                    Prefix + "prime_golden_third_order_chronology_escape"),
                H("A cubic ordered moment escapes a nontrivial step-two fiber"),
                StatementSource.FromAuthor(ThirdOrderEscapeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The words ABBA and BAAB contain the same event multiset, have the same prime-golden bidegree, and give the same complete scalar Euler trajectory.")),
                    Paragraph(Text(
                        "Their full step-two chronological signatures agree in every associative ring representation.")),
                    Paragraph(Text(
                        "Whenever the displayed cubic ordered products differ, a degree-three moment distinguishes the two histories. This supplies an explicit boundary of step-two Magnus reconstruction."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Word(params Formula[] letters)
    {
        var items = new List<Formula> { OpenBracket };
        for (var index = 0; index < letters.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
            items.Add(letters[index]);
        }
        items.Add(CloseBracket);
        return Seq([.. items]);
    }

    private static Formula CubicMoment(Formula x, Formula y)
    {
        return Seq(
            x, Sp, Cdot, Sp, y, Sp, Cdot, Sp, y, Sp, Plus, Sp,
            D(2), Sp, Cdot, Sp, Open, x, Sp, Cdot, Sp, y, Sp, Cdot, Sp, x, Close,
            Sp, Plus, Sp, y, Sp, Cdot, Sp, y, Sp, Cdot, Sp, x);
    }

    private static Formula ThirdOrderEscapeFormula()
    {
        Formula observe = F.Id("f");
        Formula u = F.Id("u");
        Formula w = F.Id("w");
        Formula fu = Call("f", u);
        Formula fw = Call("f", w);
        Formula abba = Word(u, w, w, u);
        Formula baab = Word(w, u, u, w);
        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, observe, Comma, Sp, Forall, Sp, u, Comma, Sp, Forall, Sp, w, Comma, RowBreak, Grp(),
            CubicMoment(fu, fw), Sp, Neq, Sp, CubicMoment(fw, fu),
            Sp, Rightarrow, RowBreak, Grp(),
            Call("primeGoldenBidegree", abba), Sp, Eq, Sp, Call("primeGoldenBidegree", baab),
            Sp, Land, Sp, Call("sameScalarTrajectory", abba, baab),
            Sp, Land, RowBreak, Grp(),
            Call("chronologicalSignature", observe, abba), Sp, Eq, Sp,
            Call("chronologicalSignature", observe, baab),
            Sp, Land, RowBreak, Grp(),
            Call("thirdOrderReadout", observe, abba), Sp, Neq, Sp,
            Call("thirdOrderReadout", observe, baab), Dot,
            End, Grp(F.Id("gathered"))));
    }

}
