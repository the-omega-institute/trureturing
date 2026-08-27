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

    private static Formula Typeclass(Formula proposition) =>
        Seq(OpenBracket, proposition, CloseBracket);

    private static Formula ObstructionFormula()
    {
        Formula scalar = F.Id("K"), space = F.Id("H"), index = F.Id("I");
        Formula filter = F.Id("stageFilter"), stages = F.Id("S"), stage = F.Id("i");
        Formula proper = F.Id("hProper");
        Formula stageSpace = Apply(stages, stage);
        Formula submodule = Seq(
            Operatorname, Grp(F.Id("Submodule")), Underscore, Grp(scalar),
            Open, space, Close);
        Formula residualOperator = Seq(
            Call("id", scalar, space), Sp, Minus, Sp, Call("starProjection", stageSpace));
        Formula residualNorm = new Formula.Norm(residualOperator);
        Formula stagewiseProjection = Seq(
            Forall, Sp, stage, Colon, Sp, index, Comma, Sp,
            Call("HasOrthogonalProjection", stageSpace));
        Formula properLaw = Seq(
            Forall, Sp, stage, Colon, Sp, index, Comma, Sp,
            stageSpace, Sp, Neq, Sp, F.Id("top"));
        Formula residualFunction = Grp(
            Lambda, Sp, stage, Colon, Sp, index, Comma, Sp, residualNorm);
        Formula nonconvergence = Seq(
            Neg, Sp, Call(
                "Tendsto", residualFunction, filter, Call("nhds", D(0))));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, scalar, Comma, Sp, space, Comma, Sp, index,
            Colon, Sp, F.Id("Type"), Comma,
            RowBreak, Grp(),
            Typeclass(Call("RCLike", scalar)), Comma, Sp,
            Typeclass(Call("NormedAddCommGroup", space)), Comma, RowBreak, Grp(),
            Typeclass(Call("InnerProductSpace", scalar, space)), Comma, RowBreak, Grp(),
            stages, Colon, Sp, index, Sp, To, Sp, submodule, Comma,
            RowBreak, Grp(),
            Typeclass(stagewiseProjection), Comma, RowBreak, Grp(),
            filter, Colon, Sp, Call("Filter", index), Comma, Sp,
            Typeclass(Call("NeBot", filter)), Comma, RowBreak,
            proper, Colon, Sp, Grp(properLaw), Comma, RowBreak,
            Open,
            Open, Forall, Sp, stage, Colon, Sp, index, Comma, Sp,
            residualNorm, Sp, Eq, Sp, D(1), Close,
            Sp, Land, RowBreak,
            nonconvergence,
            Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
