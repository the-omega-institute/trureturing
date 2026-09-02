using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity;

internal sealed class GoldenSubshiftUniformRecurrenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every observer in the golden word subshift sees each admissible finite factor "
            + "inside one recurrence window whose bound is independent of the observer "
            + "and the starting position.",
        H("Uniform Finite-Pattern Recurrence Across the Golden Subshift"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-subshift-uniform-finite-pattern-recurrence"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Complexity/GoldenSubshiftUniformRecurrence."
                        + "golden_subshift_factor_uniformly_recurrent"),
                H("Every golden-subshift observer shares the same factor recurrence bound"),
                StatementSource.FromAuthor(RecurrenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The public carrier is the existing prefix-language subshift of the "
                            + "golden word. Admissibility is membership in the existing finite "
                            + "golden factor set; neither object is redefined for this theorem.")),
                    Paragraph(Text(
                        "Use the existing explicit recurrence bound for the distinguished golden "
                            + "word. A sufficiently long prefix of an arbitrary subshift member "
                            + "is itself a golden factor, so an occurrence in the corresponding "
                            + "golden-word window transports back to the observer.")),
                    Paragraph(Text(
                        "The transported start lies at or after the requested index, and its end "
                            + "lies within the same bound. Thus the witness is uniform in both the "
                            + "observer and the orbit-segment start."))),
                DescribeRole.Theorem))));

    private static Formula RecurrenceFormula()
    {
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula n = F.Id("n");
        Formula w = F.Id("w");
        Formula bound = F.Id("R");
        Formula observer = F.Id("y");
        Formula start = F.Id("i");
        Formula occurrence = F.Id("j");
        Formula boolWords = Call("List", F.Id("Bool"));
        Formula observers = new Formula.TypeArrow(naturals, F.Id("Bool"));

        return Disp(Seq(
            Forall, Sp, n, InMacro, Sp, naturals, Comma, Sp,
            w, InMacro, Sp, boolWords, Comma,
            RowBreak, Grp(),
            w, Sp, InMacro, Sp, Call("goldenFactorSet", n), Sp,
            Rightarrow, Sp, Exists, Sp, bound, InMacro, Sp, naturals, Comma,
            RowBreak, Grp(),
            Forall, Sp, observer, Sp, Colon, Sp, observers, Comma, Sp,
            observer, Sp, InMacro, Sp, Call("wordSubshift", F.Id("goldenWord")), Sp,
            Rightarrow,
            RowBreak, Grp(),
            Forall, Sp, start, InMacro, Sp, naturals, Comma, Sp,
            Exists, Sp, occurrence, InMacro, Sp, naturals, Comma,
            RowBreak, Grp(),
            start, Sp, Leq, Sp, occurrence, Sp, Land, Sp,
            occurrence, Sp, Plus, Sp, n, Sp, Leq, Sp,
            start, Sp, Plus, Sp, bound, Sp, Land, Sp,
            w, Sp, Eq, Sp, Call("ofFn", Call("wordFactor", observer, n, occurrence))));
    }

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
}
