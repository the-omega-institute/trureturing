using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Automata;

internal sealed class FiniteSampleRestrictionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unsatisfiability on any exact finite subsample implies nonexistence of "
            + "a globally correct DFAO on the same state carrier.",
        H("Finite Sample Restriction"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-unsat-implies-global-unsat"),
            DeclarationHandle.Create(
                "D5/S0/Automata/FiniteSampleRestriction.no_global_fin_model_of_no_subsample_fin_model"),
            H("Finite sample UNSAT implies global nonexistence"),
            StatementSource.FromAuthor(Disp(Seq(
                Neg, Sp, Exists, Sp, F.Id("M"), Colon, Sp,
                Call("FitsSubsample", F.Id("M"), F.Id("S")),
                Sp, Rightarrow, Sp,
                Neg, Sp, Exists, Sp, F.Id("M"), Colon, Sp,
                Call("CorrectOnFamily", F.Id("M")), Dot))),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Every globally correct machine restricts to every selected family of sample indices.")),
                Paragraph(Text(
                    "Consequently a certified finite-sample exclusion is already a sound lower-bound certificate for the infinite sparse family on the same state carrier.")),
                Paragraph(Text(
                    "The converse is deliberately absent: fitting a finite sample does not establish global correctness."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S0/Automata/DFAOStateLowerBound")),
        ]));

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
