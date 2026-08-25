using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Dynamics;

internal sealed class InterventionCompletionNaturalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every controlled intervention commutes with the canonical completion projection on diagonals.",
        H("Intervention Completion Naturality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("all-interventions-commute-with-completion-projection"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Dynamics/InterventionCompletionNaturality."
                        + "all_interventions_completion_naturality"),
                H("All interventions descend naturally to completion"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The table is updated on its diagonal by the chosen controlled "
                            + "intervention. The existing pointwise table and output projections "
                            + "use the canonical controlled behavior completion projection, while "
                            + "completionUpdate is its induced quotient transition.")),
                    Paragraph(Text(
                        "For every intervention and every table, projecting the updated diagonal "
                            + "equals updating the projected diagonal. The identity is pointwise "
                            + "and follows from the quotient map computation rule."))),
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
        Formula address = F.Id("A");
        Formula controls = F.Id("U");
        Formula state = F.Id("Y");
        Formula output = F.Id("O");
        Formula update = F.Id("update");
        Formula readout = F.Id("readout");
        Formula table = F.Id("table");
        Formula control = F.Id("u");
        Formula projection = Apply("completionProjection", update, readout);
        Formula diagonal = Apply("diagonalUpdate", Apply(update, control), table);
        Formula projectedDiagonal = Apply("pointwiseOutputProjection", projection, diagonal);
        Formula projectedTable = Apply("pointwiseTableProjection", projection, table);
        Formula inducedUpdate = Apply("completionUpdate", update, readout, control);
        Formula right = Apply("diagonalUpdate", inducedUpdate, projectedTable);

        return Disp(Seq(
            Forall, Sp, address, Comma, Sp, controls, Comma, Sp, state, Comma, Sp, output,
            Comma, Sp, update, Colon, Sp, controls, Sp, To, Sp, state, Sp, To, Sp, state,
            Comma, Sp, readout, Colon, Sp, state, Sp, To, Sp, output, Comma, Sp,
            table, Colon, Sp, address, Times, Sp, address, Sp, To, Sp, state, Comma, Sp,
            Forall, Sp, control, InMacro, Sp, controls, Comma, Sp,
            projectedDiagonal, Sp, Eq, Sp, right, Dot));
    }
}
