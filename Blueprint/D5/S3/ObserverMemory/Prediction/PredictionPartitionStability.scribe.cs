using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Prediction;

internal sealed class PredictionPartitionStabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeNode.Create(
            "A prediction partition unchanged by one extra readout is unchanged at every depth.",
            H("Prediction Partition Stability"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("prediction-partition-stable-forever"),
                    DeclarationHandle.Create(
                        "D5/S3/ObserverMemory/Prediction/PredictionPartitionStability."
                        + "prediction_partition_stable_forever"),
                    H("A one-step stable prediction partition is permanently stable"),
                    StatementSource.FromAuthor(StabilityFormula()),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "For a self-map F and readout q, ReadoutWord(F,q,m,y) records the "
                            + "readouts of y at update times zero through m. The hypothesis says "
                            + "that equality of these words is exactly the same relation at "
                            + "depths m and m+1.")),
                        Paragraph(Text(
                            "The first conjunct proves that this depth-m relation is preserved "
                            + "when both states are updated by F. Iterating that congruence makes "
                            + "every later readout agree, while truncation gives the reverse "
                            + "implication. Thus the relation at every depth m+r equals the "
                            + "relation at depth m.")),
                        Paragraph(Text(
                            "Repository search found the exact finite-word definition but no "
                            + "theorem containing both conclusions. Pinned Mathlib and Loogle "
                            + "found Function.iterate_add_apply, which the proof applies to "
                            + "shift readout coordinates. LeanSearch's shaped endpoint returned "
                            + "HTTP 404 and supplied no result.")),
                        Paragraph(Text(
                            "The theorem is general in both types and does not require "
                            + "finiteness. A constant Boolean readout gives a checked witness "
                            + "that the stabilization hypothesis is satisfiable on a nontrivial "
                            + "state carrier."))),
                    DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Word(Formula depth, Formula state) =>
        Call("ReadoutWord", F.Id("F"), F.Id("q"), depth, state);

    private static Formula StabilityFormula()
    {
        Formula stateType = F.Id("Y");
        Formula outputType = F.Id("O");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
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
            Forall, Sp, stateType, Comma, Sp, outputType, Colon, Sp, type, Comma, Esc,
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
