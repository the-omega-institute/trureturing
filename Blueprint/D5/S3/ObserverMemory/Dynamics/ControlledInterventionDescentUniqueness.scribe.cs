using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Dynamics;

internal sealed class ControlledInterventionDescentUniquenessDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every controlled update descends uniquely through canonical behavior completion.",
        H("Controlled Intervention Descent Uniqueness"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("all-controlled-updates-descend-uniquely"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Dynamics/ControlledInterventionDescentUniqueness."
                        + "all_interventions_unique_completion_descent"),
                H("All controlled updates descend uniquely"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The carrier is the canonical quotient by equality of every finite-word "
                            + "readout, and pi is its canonical projection. No separate "
                            + "completion or projection primitive is introduced.")),
                    Paragraph(Text(
                        "For every control u, there is exactly one endomap of the completion "
                            + "that makes the update square commute. Existence is witnessed by "
                            + "the canonical completion update; uniqueness follows from "
                            + "surjectivity of the quotient projection.")),
                    Paragraph(Text(
                        "Pointwise table and output projections lift this unique underlying "
                            + "square to the source's simultaneous diagonal naturality law."))),
                DescribeRole.Theorem))));

    private static Formula Apply(string name, params Formula[] arguments)
    {
        var content = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
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

    private static Formula Apply(Formula name, params Formula[] arguments)
    {
        var content = new List<Formula> { name, Open };
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
        Formula controls = F.Id("U");
        Formula states = F.Id("Y");
        Formula outputs = F.Id("O");
        Formula update = F.Id("F");
        Formula readout = F.Id("q");
        Formula control = F.Id("u");
        Formula projection = Pi;
        Formula descended = Seq(Overline, Grp(F.Id("F")), Underscore, Grp(control));
        Formula completion = Apply("ControlledCompletion", update, readout);
        Formula controlledUpdate = Apply(update, control);

        return Disp(Seq(
            Forall, Sp, states, Comma, Sp, controls, Comma, Sp, outputs, Comma, Esc,
            update, Colon, Sp, controls, Sp, To, Sp, states, Sp, To, Sp, states,
            Comma, Sp, readout, Colon, Sp, states, Sp, To, Sp, outputs, Comma, Esc,
            Forall, Sp, control, InMacro, Sp, controls, Comma, Sp,
            Exists, Bang, Sp, descended, Colon, Sp,
            completion, Sp, To, Sp, completion, Comma, RowBreak,
            Grp(), projection, Sp, Circ, Sp, controlledUpdate, Sp, Eq, Sp,
            descended, Sp, Circ, Sp, projection, Dot));
    }
}
