using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Characterizations;

internal sealed class GoldenDisplacementSeriesValueSetDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/Analytic/Characterizations/GoldenDisplacementSeriesValueSet.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The values attained by convergent golden displacement series form exactly the open "
        + "ray above one.",
        H("Value Set of the Golden Displacement Series"),
        Blocks(
            Paragraph(Text(
                "Every convergent golden displacement series has value strictly greater than "
                + "one. Conversely, finite harmonic sums become arbitrarily large. On the "
                + "zero first-parameter slice, exponents approaching one from above produce "
                + "convergent p-series whose finite partial sums approach those harmonic sums.")),
            Describe.Lean(
                DescribeId.Create("golden-displacement-series-values-open-ray"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "golden_displacement_series_values_eq_Ioi_one"),
                H("The attained value set is the open ray above one"),
                StatementSource.FromAuthor(ValueSetFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Given any real x greater than one, choose a finite harmonic sum above "
                        + "x. Continuity in its exponent supplies a p-series exponent greater "
                        + "than one whose matching finite sum still exceeds x. Summability and "
                        + "termwise nonnegativity put the full p-series sum above x.")),
                    Paragraph(Text(
                        "That full sum is an attained golden displacement value on the zero "
                        + "slice. The established no-gap theorem then fills the interval from "
                        + "one to this attained value, proving that x is attained.")),
                    Paragraph(Text(
                        "This theorem classifies only the set of attained real values. It does "
                        + "not identify which parameter pairs attain a given value, assert "
                        + "uniqueness of parameters, give convergence rates, or claim that a "
                        + "series converges at the boundary exponent one."))),
                DescribeRole.Theorem))));

    private static Formula ValueSetFormula() =>
        F.Disp(F.Seq(FullValueSet(), F.Sp, F.Eq, F.Sp, Call("Ioi", F.D(1)), F.Dot));

    private static Formula FullValueSet()
    {
        Formula x = F.Id("x");
        Formula s = F.Id("s");
        Formula w = F.Id("w");
        return F.Seq(
            F.Left, F.OpenBrace, x, F.Sp, F.Colon, F.Sp, Reals(),
            F.Sp, F.Mid, F.Sp,
            F.Exists, F.Sp, s, F.Comma, F.Sp, w,
            F.Sp, F.InMacro, F.Sp, Reals(), F.Comma, F.Sp,
            Call("Summable", Call("dTerm", s, w)),
            F.Sp, F.Land, F.RowBreak,
            Tsum(s, w), F.Sp, F.Eq, F.Sp, x,
            F.Right, F.CloseBrace);
    }

    private static Formula Reals() => F.Seq(F.Mathbb, F.Grp(F.Id("R")));

    private static Formula Tsum(Formula s, Formula w)
    {
        Formula n = F.Id("n");
        return F.Seq(
            F.Sum, F.Underscore, F.Grp(n, F.Eq, F.D(0)),
            F.Caret, F.Grp(F.Infty), F.Sp, Call("dTerm", s, w, n));
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var pieces = new List<Formula> { F.Operatorname, F.Grp(F.Id(name)), F.Open };
        for (int index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                pieces.Add(F.Comma);
                pieces.Add(F.Sp);
            }

            pieces.Add(arguments[index]);
        }

        pieces.Add(F.Close);
        return F.Seq(pieces.ToArray());
    }
}
