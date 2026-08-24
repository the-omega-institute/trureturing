using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Experiments;

internal sealed class TargetRelativeExperimentSuperiorityDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Experiments/TargetRelativeExperimentSuperiority."
            + "incomparable_experiments_have_opposite_target_advantages";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Incomparable experiments each serve a target that the other does not.",
        H("Target-Relative Experiment Superiority"),
        Blocks(Describe.Lean(
            DescribeId.Create("incomparable-experiments-have-opposite-target-advantages"),
            DeclarationHandle.Create(Declaration),
            H("Incomparable experiments have opposite target advantages"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Choose the first experiment itself as the first target. Reflexivity makes "
                        + "that target available from the first experiment, while the assumed "
                        + "non-refinement excludes it from the second.")),
                Paragraph(Text(
                    "Choosing the second experiment itself gives the symmetric witness. Both "
                        + "directional target advantages occur in the public conclusion."))),
            DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula Sub(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula Refines(Formula coarse, Formula fine) =>
        Call("Refines", coarse, fine);

    private static Formula Advantage(Formula target, Formula preferred, Formula other) =>
        Seq(Refines(target, preferred), Sp, Land, Sp,
            Neg, Sp, Refines(target, other));

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula one = D(1);
        Formula two = D(2);
        Formula firstType = Sub(F.Id("E"), one);
        Formula secondType = Sub(F.Id("E"), two);
        Formula first = Sub(F.Id("q"), one);
        Formula second = Sub(F.Id("q"), two);
        Formula firstTarget = Sub(F.Id("t"), one);
        Formula secondTarget = Sub(F.Id("t"), two);
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));

        Formula firstWitness = Seq(
            Exists, Sp, firstTarget, Colon, Sp, Arrow(state, firstType), Comma, Sp,
            Advantage(firstTarget, first, second));
        Formula secondWitness = Seq(
            Exists, Sp, secondTarget, Colon, Sp, Arrow(state, secondType), Comma, Sp,
            Advantage(secondTarget, second, first));

        return Disp(Seq(
            Forall, Sp, state, Comma, Sp, firstType, Comma, Sp, secondType,
            Colon, Sp, type, Comma, RowBreak, Grp(),
            first, Colon, Sp, Arrow(state, firstType), Comma, Sp,
            second, Colon, Sp, Arrow(state, secondType), Comma, RowBreak, Grp(),
            Open, Neg, Sp, Refines(first, second), Sp, Land, Sp,
            Neg, Sp, Refines(second, first), Close, Sp, Rightarrow, RowBreak, Grp(),
            Open, Open, firstWitness, Close, Sp, Land, Sp,
            Open, secondWitness, Close, Close, Dot));
    }
}
