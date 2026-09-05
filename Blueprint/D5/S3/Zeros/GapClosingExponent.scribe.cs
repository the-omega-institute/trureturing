using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros;

internal sealed class GapClosingExponentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nonzero leading term fixes the punctured gap-closing exponent.",
        H("Gap-Closing Exponent"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gap-closing-exponent"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/GapClosingExponent.gap_closing_exponent"),
                H("The normalized gap converges to its positive leading coefficient"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix the transverse coordinate. Let V have leading term equal to the "
                            + "squared modulus of a nonzero complex coefficient times the absolute "
                            + "displacement to the power 2m, with a little-o residual.")),
                    Paragraph(Text(
                        "The multiplicity is positive. On the punctured neighborhood the power "
                            + "never vanishes, and dividing the little-o residual by it tends to "
                            + "zero. Hence the normalized gap tends to the strictly positive "
                            + "squared modulus, which records the exact visible exponent 2m."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula V = F.Id("V");
        Formula c = F.Id("c");
        Formula tStar = F.Id("tStar");
        Formula t = F.Id("t");
        Formula m = F.Id("m");
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula complexes = Seq(Mathbb, Grp(F.Id("C")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula gapFunction = Arrow(reals, reals);
        Formula displacement = Call("abs", Seq(t, Sp, Minus, Sp, tStar));
        Formula exponent = Seq(D(2), Sp, Times, Sp, m);
        Formula scale = Seq(displacement, Caret, Grp(exponent));
        Formula coefficient = Call("normSq", c);
        Formula residual = Seq(
            Apply(V, t), Sp, Minus, Sp,
            coefficient, Sp, Times, Sp, scale);
        Formula residualFunction = Lambda(t, reals, residual);
        Formula scaleFunction = Lambda(t, reals, scale);
        Formula normalized = Lambda(
            t, reals, new Formula.Fraction(Apply(V, t), scale));

        Formula assumptions = Seq(
            D(0), Sp, Lt, Sp, m, Sp, Land, Sp,
            c, Sp, Neq, Sp, D(0), Sp, Land, Sp,
            Call("IsLittleOAt", tStar, residualFunction, scaleFunction));
        Formula conclusion = Seq(
            Call(
                "Tendsto",
                normalized,
                Call("puncturedNhds", tStar),
                Call("nhds", coefficient)),
            Sp, Land, Sp,
            D(0), Sp, Lt, Sp, coefficient);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, Typed(V, gapFunction), Comma, Sp,
                Typed(c, complexes), Comma, Sp,
                Typed(tStar, reals), Comma, Sp,
                Typed(m, naturals), Comma),
            Seq(Grp(), assumptions, Sp, Rightarrow, Sp, conclusion, Dot),
        ]));
    }

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Lambda(Formula name, Formula type, Formula body) =>
        Seq(Open, name, Colon, Sp, type, Sp, Mapsto, Sp, body, Close);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var item = 0; item < arguments.Length; item++)
        {
            if (item > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[item]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }
}
