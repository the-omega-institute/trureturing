using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Sufficiency;

internal sealed class PredictiveSufficiencyDescentDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Sufficiency/PredictiveSufficiencyDescent."
            + "predictive_sufficiency_descent";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Predictive completion carries the update and the current readout.",
        H("Predictive Sufficiency Descent"),
        Blocks(Describe.Lean(
            DescribeId.Create("predictive-sufficiency-descent"),
            DeclarationHandle.Create(Declaration),
            H("The update and readout descend to predictive completion"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The completion carrier is the canonical quotient by equality of complete "
                        + "future readout itineraries. Its projection, update, and readout are the "
                        + "existing family primitives.")),
                Paragraph(Text(
                    "The first public equation gives the induced update on every quotient class. "
                        + "The second gives the descended current readout on the same canonical "
                        + "class; neither object is reconstructed in this module."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula TheoremFormula()
    {
        Formula stateType = F.Id("X");
        Formula outputType = F.Id("O");
        Formula update = F.Id("F");
        Formula readout = F.Id("q");
        Formula state = F.Id("x");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula projection = Call("completionProjection", update, readout);
        Formula inducedUpdate = Call("completionUpdate", update, readout);
        Formula inducedReadout = Call("completionReadout", update, readout);
        Formula stateClass = Apply(projection, state);

        return Disp(Seq(
            Forall, Sp, stateType, Comma, Sp, outputType, Colon, Sp, type,
            Comma, Sp,
            update, Colon, Sp, stateType, Sp, To, Sp, stateType, Comma, Sp,
            readout, Colon, Sp, stateType, Sp, To, Sp, outputType, Comma,
            RowBreak, Grp(),
            Open, Forall, Sp, state, Comma, Sp,
            Apply(inducedUpdate, stateClass), Sp, Eq, Sp,
            Apply(projection, Apply(update, state)), Close,
            Sp, Land,
            RowBreak, Grp(),
            Open, Forall, Sp, state, Comma, Sp,
            Apply(inducedReadout, stateClass), Sp, Eq, Sp,
            Apply(readout, state), Close, Dot));
    }
}
