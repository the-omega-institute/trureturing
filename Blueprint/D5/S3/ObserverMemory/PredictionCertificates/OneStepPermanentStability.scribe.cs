using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.PredictionCertificates;

internal sealed class OneStepPermanentStabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A prediction partition stable for one step remains stable at every later depth.",
        H("One-Step Permanent Stability"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("one-step-stability-is-permanent"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/PredictionCertificates/OneStepPermanentStability."
                        + "one_step_stability_is_permanent"),
                H("One stable step makes every later prediction relation equal"),
                StatementSource.FromAuthor(StabilityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a self-map F and readout q, ReadoutWord(F,q,m,y) records the "
                            + "readouts of y at update times zero through m. The premise states "
                            + "that equality of words at depths m and m+1 defines the same "
                            + "relation on states.")),
                    Paragraph(Text(
                        "The first public conjunct says that the depth-m relation is preserved "
                            + "by updating both states. The second says, for every natural offset "
                            + "r, that equality at depth m+r is equivalent to equality at depth m.")),
                    Paragraph(Text(
                        "Repository search found prediction_partition_stable_forever with exactly "
                            + "this premise and both conclusions. The Lean wrapper imports and "
                            + "applies that declaration directly, without introducing another "
                            + "prediction-word or relation primitive.")),
                    Paragraph(Text(
                        "The imported module also compiles a constant Boolean readout witness for "
                            + "the premise, so the hypothesis is satisfiable on an inhabited, "
                            + "nontrivial state carrier."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Word(Formula depth, Formula state) =>
        Call("ReadoutWord", F.Id("F"), F.Id("q"), depth, state);

    private static Formula StabilityFormula()
    {
        Formula stateType = F.Id("Y");
        Formula outputType = F.Id("O");
        Formula y = F.Id("y");
        Formula yPrime = Seq(F.Id("y"), Apos);
        Formula depth = F.Id("m");
        Formula offset = F.Id("r");
        Formula sameAtDepth = Seq(
            Word(depth, y), Sp, Eq, Sp, Word(depth, yPrime));
        Formula sameAtNext = Seq(
            Word(Seq(depth, Plus, D(1)), y), Sp, Eq, Sp,
            Word(Seq(depth, Plus, D(1)), yPrime));
        Formula preserved = Seq(
            Word(depth, Apply(F.Id("F"), y)), Sp, Eq, Sp,
            Word(depth, Apply(F.Id("F"), yPrime)));
        Formula sameLater = Seq(
            Word(Seq(depth, Plus, offset), y), Sp, Eq, Sp,
            Word(Seq(depth, Plus, offset), yPrime));

        return Disp(Seq(
            Forall, Sp, stateType, Comma, Sp, outputType, Comma, Esc,
            F.Id("F"), Colon, Sp, stateType, Sp, To, Sp, stateType,
            Comma, Sp, F.Id("q"), Colon, Sp, stateType, Sp, To, Sp,
            outputType, Comma, Sp, depth, InMacro, Sp,
            Mathbb, Grp(F.Id("N")), Comma, Esc,
            Open, Forall, Sp, y, Comma, Sp, yPrime, Comma, Esc,
            sameAtDepth, Sp, Iff, Sp, sameAtNext, Close, Sp,
            Implies, Sp, Left, Open,
            Open, Forall, Sp, y, Comma, Sp, yPrime, Comma, Esc,
            sameAtDepth, Sp, Rightarrow, Sp, preserved, Close,
            Sp, Land, Sp,
            Open, Forall, Sp, offset, InMacro, Sp,
            Mathbb, Grp(F.Id("N")), Comma, Sp, y, Comma, Sp, yPrime,
            Comma, Esc, sameLater, Sp, Iff, Sp, sameAtDepth, Close,
            Right, Close, Dot));
    }
}
