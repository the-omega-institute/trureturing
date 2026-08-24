using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Completion;

internal sealed class UniformCompletionObstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Proper Hilbert-subspace projections remain one operator-norm unit from the identity.",
        H("Uniform Completion Obstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("proper-projection-stages-cannot-complete-in-operator-norm"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Completion/UniformCompletionObstruction."
                        + "uniform_completion_obstruction"),
                H("Proper projection stages stay uniformly separated from identity"),
                StatementSource.FromAuthor(ObstructionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let S be a family of proper closed subspaces of a Hilbert space, "
                            + "indexed along a nontrivial stage filter, and let each stage map be "
                            + "its canonical orthogonal projection.")),
                    Paragraph(Text(
                        "Identity minus the stage projection is the orthogonal projection onto "
                            + "the nonzero complementary subspace. Its operator norm is exactly "
                            + "one at every stage.")),
                    Paragraph(Text(
                        "Consequently the operator-norm distances cannot converge to zero along "
                            + "the stage filter."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula ObstructionFormula()
    {
        Formula scalar = F.Id("K"), space = F.Id("H"), index = F.Id("A");
        Formula filter = F.Id("L"), stages = F.Id("S"), stage = F.Id("a");
        Formula stageSpace = Apply(stages, stage);
        Formula residualOperator = Seq(F.Id("I"), Sp, Minus, Sp, Call("P", stageSpace));
        Formula residualNorm = new Formula.Norm(residualOperator);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, scalar, Comma, Sp, space, Comma, Sp, index, Comma, Sp, filter, Comma,
            RowBreak,
            Call("Hilbert", scalar, space), Comma, Sp, Call("NeBot", filter), Comma, Sp,
            stages, Colon, Sp, index, Sp, To, Sp, Call("ClosedSubspace", space), Comma,
            RowBreak,
            Open, Forall, Sp, stage, Comma, Sp, stageSpace, Sp, Neq, Sp, space, Close,
            Sp, Implies, Sp, RowBreak,
            Open,
            Open, Forall, Sp, stage, Comma, Sp, residualNorm, Sp, Eq, Sp, D(1), Close,
            Sp, Land, RowBreak,
            Neg, Sp, Open, Call("lim", stage, filter, residualNorm), Sp, Eq, Sp, D(0), Close,
            Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
