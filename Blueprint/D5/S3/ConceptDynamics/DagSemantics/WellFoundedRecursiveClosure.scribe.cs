using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DagSemantics;

internal sealed class WellFoundedRecursiveClosureDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/DagSemantics/WellFoundedRecursiveClosure.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Well-founded dependency equations have unique solutions, while a self-loop admits a "
            + "fixed-point gap.",
        H("Well-Founded Recursive Closure"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("well-founded-equations-have-unique-solutions"),
                DeclarationHandle.Create(Prefix + "dependencyEquation_solution_unique"),
                H("Well-founded dependency equations have unique solutions"),
                StatementSource.FromAuthor(UniquenessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume the dependency relation is well-founded and two sets both solve "
                            + "the same local equation with the same seed. The two solution sets "
                            + "are equal.")),
                    Paragraph(Text(
                        "Well-foundedness and both solution predicates are displayed antecedents. "
                            + "The theorem establishes uniqueness, not existence of a solution."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("self-loop-has-a-fixed-point-gap"),
                DeclarationHandle.Create(Prefix + "selfLoop_has_fixedPoint_gap"),
                H("The unseeded self-loop has two distinct solutions"),
                StatementSource.FromAuthor(SelfLoopFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For the one-point self-loop and empty seed, there exist two distinct sets "
                            + "that satisfy the dependency equation.")),
                    Paragraph(Text(
                        "The witnesses are existentially packaged. The theorem states their "
                            + "distinctness and both solution conditions without claiming that "
                            + "every non-well-founded relation has this gap."))),
                DescribeRole.Theorem))));

    private static Formula UniquenessFormula()
    {
        Formula edge = F.Id("edge");
        Formula seed = F.Id("seed");
        Formula first = F.Id("first");
        Formula second = F.Id("second");
        Formula hypotheses = Seq(
            Call("WellFounded", edge), Sp, Land, Sp,
            Call("SatisfiesDependencyEquation", edge, seed, first), Sp, Land,
            RowBreak, Grp(),
            Call("SatisfiesDependencyEquation", edge, seed, second));

        return Disp(Seq(
            Forall, Sp, edge, Colon, Sp,
            F.Id("V"), Sp, To, Sp, F.Id("V"), Sp, To, Sp, F.Id("Prop"), Comma, Sp,
            seed, Comma, Sp, first, Comma, Sp, second, Colon, Sp, Call("Set", F.Id("V")),
            Comma, RowBreak, Grp(), Open, hypotheses, Close, Sp, Rightarrow,
            RowBreak, Grp(), first, Sp, Eq, Sp, second, Dot));
    }

    private static Formula SelfLoopFormula()
    {
        Formula first = F.Id("first");
        Formula second = F.Id("second");
        Formula consequence = Seq(
            first, Sp, Neq, Sp, second, Sp, Land, RowBreak, Grp(),
            Call("SatisfiesDependencyEquation", F.Id("selfLoop"), Emptyset, first),
            Sp, Land, RowBreak, Grp(),
            Call("SatisfiesDependencyEquation", F.Id("selfLoop"), Emptyset, second));

        return Disp(Seq(
            Exists, Sp, first, Comma, Sp, second, Colon, Sp, Call("Set", F.Id("Unit")),
            Comma, RowBreak, Grp(), Open, consequence, Close, Dot));
    }
}
