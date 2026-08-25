using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.MeasureSeparation;

internal sealed class SingularProbabilityPerfectSeparatorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mutually singular probability laws admit a measurable perfect separator.",
        H("Singular Probability Laws Have Perfect Separation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("mutually-singular-probability-laws-have-perfect-separator"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/MeasureSeparation/"
                        + "SingularProbabilityPerfectSeparator."
                        + "mutually_singular_probability_laws_have_perfect_separator"),
                H("A measurable event separates singular laws with zero error"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The two state-indexed transcript laws are probability measures on one "
                            + "measurable transcript space. Their mutual singularity is the "
                            + "product-singular premise established immediately before the "
                            + "source theorem.")),
                    Paragraph(Text(
                        "Mathlib's canonical singular set is measurable, null under the first "
                            + "law, and has null complement under the second law. Its complement "
                            + "is therefore the required event.")),
                    Paragraph(Text(
                        "The probability-measure instance turns nullity of the singular set into "
                            + "mass one for its complement. Thus the complete transcript "
                            + "distinguishes the two laws outside null sets.")),
                    Paragraph(Text(
                        "Repository searches found only special or premise-heavier separation "
                            + "results. The proof applies the pinned measurable singular-set API "
                            + "directly."))),
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
        Formula eventSet = Seq(F.Id("A"), Underscore, Grp(F.Id("x"), Comma, F.Id("y")));
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula measure = Call("Measure", transcript);
        Formula assumptions = Seq(
            Call("ProbabilityMeasure", probabilityX), Sp, Land, Sp,
            Call("ProbabilityMeasure", probabilityY), Sp, Land, Sp,
            Call("MutuallySingular", probabilityX, probabilityY));
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
            assumptions, RowBreak, Grp(),
            Rightarrow, Sp, Exists, Sp, eventSet, Colon, Sp,
            Call("Set", transcript), Comma, Sp, separator, Dot));
    }
}
