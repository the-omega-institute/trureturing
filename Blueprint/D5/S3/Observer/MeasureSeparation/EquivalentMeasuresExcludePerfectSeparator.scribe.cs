using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.MeasureSeparation;

internal sealed class EquivalentMeasuresExcludePerfectSeparatorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equivalent probability laws admit no measurable event separating them with zero error.",
        H("Equivalent Laws Exclude Perfect Separation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("equivalent-probability-laws-exclude-perfect-separator"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/MeasureSeparation/"
                        + "EquivalentMeasuresExcludePerfectSeparator."
                        + "equivalent_probability_laws_exclude_perfect_separator"),
                H("There is no zero-error separating event"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The two state-indexed transcript laws are probability measures on one "
                            + "measurable transcript space. Product equivalence is exposed as "
                            + "absolute continuity in both directions.")),
                    Paragraph(Text(
                        "If the second law assigns a measurable event mass zero, absolute "
                            + "continuity forces the first law to assign it mass zero as well. "
                            + "It therefore cannot simultaneously have mass one under the first "
                            + "law.")),
                    Paragraph(Text(
                        "The opposite singular regime is intentionally excluded: mutually "
                            + "singular laws can have measurable full-versus-null separating "
                            + "events.")),
                    Paragraph(Text(
                        "Repository searches found no exact D5 theorem. The proof directly applies "
                            + "Mathlib's absolute-continuity null-set transport primitive."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula TheoremFormula()
    {
        Formula transcript = F.Id("Omega");
        Formula probabilityX = Seq(F.Id("P"), Underscore, Grp(F.Id("x")));
        Formula probabilityY = Seq(F.Id("P"), Underscore, Grp(F.Id("y")));
        Formula eventSet = F.Id("A");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula measure = Call("Measure", transcript);
        Formula equivalent = Seq(
            Call("AbsolutelyContinuous", probabilityX, probabilityY), Sp, Land, Sp,
            Call("AbsolutelyContinuous", probabilityY, probabilityX));
        Formula separator = Seq(
            Call("Measurable", eventSet), Sp, Land, Sp,
            Apply(probabilityX, eventSet), Sp, Eq, Sp, D(1), Sp, Land, Sp,
            Apply(probabilityY, eventSet), Sp, Eq, Sp, D(0));

        return Disp(Seq(
            Forall, Sp, transcript, Colon, Sp, type, Comma, Sp,
            OpenBracket, Call("MeasurableSpace", transcript), CloseBracket,
            Comma, RowBreak, Grp(),
            probabilityX, Comma, Sp, probabilityY, Colon, Sp, measure,
            Comma, RowBreak, Grp(),
            Call("ProbabilityMeasure", probabilityX), Sp, Land, Sp,
            Call("ProbabilityMeasure", probabilityY), Sp, Land, Sp,
            equivalent, RowBreak, Grp(),
            Rightarrow, Sp, Neg, Exists, Sp, eventSet, Colon, Sp,
            Call("Set", transcript), Comma, Sp, separator, Dot));
    }
}
