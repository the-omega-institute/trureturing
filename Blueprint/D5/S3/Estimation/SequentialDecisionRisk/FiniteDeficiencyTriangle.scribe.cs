using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.SequentialDecisionRisk;

internal sealed class FiniteDeficiencyTriangleDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Estimation/SequentialDecisionRisk/FiniteDeficiencyTriangle."
            + "finite_deficiency_triangle";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One-way finite experiment deficiency satisfies the triangle inequality under simulator composition.",
        H("Finite Deficiency Triangle"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-deficiency-triangle"),
            DeclarationHandle.Create(Declaration),
            H("Finite deficiency obeys the triangle inequality"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "Two row-stochastic simulators compose to a row-stochastic simulator. The "
                    + "total-variation triangle inequality and channel contraction bound its error, "
                    + "and independent infima give the stated deficiency inequality."))),
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

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("Theta");
        Formula firstObservation = F.Id("X");
        Formula middleObservation = F.Id("Y");
        Formula finalObservation = F.Id("Z");
        Formula first = F.Id("E");
        Formula middle = F.Id("F");
        Formula final = F.Id("G");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, firstObservation, Comma, Sp,
            middleObservation, Comma, Sp, finalObservation, Colon, Sp, F.Id("Type"), Comma,
            RowBreak, Grp(),
            Call("Fintype", state), Sp, Land, Sp, Call("Nonempty", state), Sp, Land, Sp,
            Call("Fintype", firstObservation), Sp, Land, Sp,
            Call("Fintype", middleObservation), Sp, Land, Sp,
            Call("Fintype", finalObservation), Comma, RowBreak, Grp(),
            first, Colon, Sp, Call("FiniteMarkovKernel", state, firstObservation), Comma, Sp,
            middle, Colon, Sp, Call("FiniteMarkovKernel", state, middleObservation), Comma, Sp,
            final, Colon, Sp, Call("FiniteMarkovKernel", state, finalObservation), Sp,
            Rightarrow, RowBreak, Grp(),
            Call("finiteDeficiency", final, first), Sp, Leq, Sp,
            Call("finiteDeficiency", final, middle), Sp, Plus, Sp,
            Call("finiteDeficiency", middle, first), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
