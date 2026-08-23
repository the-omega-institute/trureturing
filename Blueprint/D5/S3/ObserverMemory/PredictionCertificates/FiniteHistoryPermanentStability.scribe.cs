using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.PredictionCertificates;

internal sealed class FiniteHistoryPermanentStabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite-history relation stable at one consecutive depth remains permanently stable.",
        H("Finite-History Permanent Stability"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-history-relation-stable-forever"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/PredictionCertificates/"
                        + "FiniteHistoryPermanentStability."
                        + "finite_history_relation_stable_forever"),
                H("One stable depth makes all later history relations equal"),
                StatementSource.FromAuthor(StatementFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let F be a self-map and q a readout. ReadoutWord(F,q,m,y) is the "
                            + "finite observation history of y through update depth m, so "
                            + "equality of such words constructs the source relation directly.")),
                    Paragraph(Text(
                        "If equality at depth m is equivalent to equality at depth m+1, then "
                            + "for every natural offset r, equality at depth m is equivalent "
                            + "to equality at depth m+r.")),
                    Paragraph(Text(
                        "The exact repository theorem one_step_stability_is_permanent uses the "
                            + "same history words and premise. The Lean theorem applies its "
                            + "all-later-depth component directly."))),
                DescribeRole.Theorem))));

    private static Formula Word(Formula depth, Formula state) =>
        Call("ReadoutWord", F.Id("F"), F.Id("q"), depth, state);

    private static Formula StatementFormula()
    {
        Formula stateType = F.Id("Y");
        Formula outputType = F.Id("O");
        Formula depth = F.Id("m");
        Formula offset = F.Id("r");
        Formula y = F.Id("y");
        Formula yPrime = Seq(F.Id("y"), Apos);
        Formula sameAtDepth = Seq(Word(depth, y), Sp, Eq, Sp, Word(depth, yPrime));
        Formula sameAtNext = Seq(
            Word(Seq(depth, Plus, D(1)), y), Sp, Eq, Sp,
            Word(Seq(depth, Plus, D(1)), yPrime));
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
            Implies, Sp, Open, Forall, Sp, offset, InMacro, Sp,
            Mathbb, Grp(F.Id("N")), Comma, Sp, y, Comma, Sp, yPrime,
            Comma, Esc, sameAtDepth, Sp, Iff, Sp, sameLater, Close, Dot));
    }
}
