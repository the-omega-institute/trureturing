using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Experiment;

internal sealed class SelfCalibratingActionObstructionDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Experiment/SelfCalibratingActionObstruction."
            + "three_read_action_unbounded";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every globally valid three-read protocol has unbounded literal atomic-action cost.",
        H("Three-Read Action Obstruction"),
        Blocks(
            Paragraph(Text(
                "A source is a strictly positive rank-one real relation matrix. "
                    + "A protocol reads the empty word first, extends its literal word "
                    + "chronologically, and must terminate with the original relation.")),
            Paragraph(Text(
                "For every valid protocol and every natural bound C, a positive shear fiber "
                    + "can be selected whose common first two readings force a third literal "
                    + "continuation with cost greater than C. The source supplied by that fiber "
                    + "still has a terminating run of at most three readings.")),
            Describe.Lean(
                DescribeId.Create("self-calibrating-three-read-action-unbounded"),
                DeclarationHandle.Create(Declaration),
                H("No uniform finite action bound for three reads"),
                StatementSource.FromAuthor(StatementFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The second query is a nontrivial integral shear. Choosing the shear "
                            + "fiber parameter z as the reciprocal of a prescribed natural "
                            + "scale makes the exact third-read lower bound exceed that scale.")),
                    Paragraph(Text(
                        "The proof uses the full positive shear-fiber criterion: every compatible "
                            + "source has the same first two readings, and any successful third "
                            + "run pays the fixed prefix together with the required continuation."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);

    private static Formula StatementFormula()
    {
        Formula protocol = F.Id("P");
        Formula bound = F.Id("C");
        Formula source = F.Id("R");
        Formula fuel = F.Id("n");
        Formula history = F.Id("tr");
        Formula output = F.Id("out");
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, protocol, Comma, Sp, Call("OriginalValid", protocol), Sp,
                Rightarrow, Sp, Forall, Sp, bound, InMacro, natural, Comma, RowBreak, Grp()),
            Seq(Exists, Sp, source, Comma, Sp, fuel, Comma, Sp, history, Comma, Sp,
                output, Sp, Call("run", protocol, source, fuel, history, output), Sp,
                Land, Sp, Call("readsAtMost", history, D(3)), Sp, Land, Sp,
                Call("returns", output, source), Sp, Land, Sp,
                bound, Sp, Lt, Sp, Call("actualCost", history, output), Dot)
        ]));
    }
}
