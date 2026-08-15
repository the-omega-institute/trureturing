using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Prediction;

internal sealed class ForwardMergePersistenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeNode.Create(
            "States merged by a deterministic update have identical future states and readouts.",
            H("Forward Merge Persistence"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("merged-states-have-identical-futures"),
                    DeclarationHandle.Create(
                        "D5/S3/ObserverMemory/Prediction/ForwardMergePersistence."
                        + "forward_merge_persistence"),
                    H("Merged states have identical futures"),
                    StatementSource.FromAuthor(PersistenceFormula()),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Let F be a deterministic self-map, q any readout, and y and y' "
                            + "two states. If the states agree after t updates, then applying "
                            + "the same further r updates preserves their equality. Applying "
                            + "q to that common future state gives identical future readouts.")),
                        Paragraph(Text(
                            "The pinned library search found Function.iterate_add_apply as the "
                            + "exact decomposition of an iterate at t+r; the proof imports and "
                            + "applies it. Loogle found that declaration by name but no theorem "
                            + "matching the full persistent-equality shape. LeanSearch returned "
                            + "nearby iterate and fixed-point lemmas, but no exact result. A "
                            + "repository search found no declaration with the same hypothesis "
                            + "and conclusion.")),
                        Paragraph(Text(
                            "The theorem is general in the state and output types. It does not "
                            + "require finiteness or injectivity, and it makes no converse claim. "
                            + "A constant Boolean update supplies a checked witness in which two "
                            + "distinct initial states satisfy the merge hypothesis."))),
                    DescribeRole.Theorem))));

    private static Formula Iterate(Formula exponent, Formula state) =>
        Seq(F.Id("F"), Caret, Grp(exponent), Open, state, Close);

    private static Formula Read(Formula state) =>
        Seq(F.Id("q"), Open, state, Close);

    private static Formula PersistenceFormula()
    {
        Formula y = F.Id("y");
        Formula yPrime = Seq(F.Id("y"), Apos);
        Formula t = F.Id("t");
        Formula r = F.Id("r");
        Formula future = Seq(t, Plus, r);
        Formula futureY = Iterate(future, y);
        Formula futureYPrime = Iterate(future, yPrime);
        return Disp(Seq(
            Forall, Sp, F.Id("State"), Comma, Sp, F.Id("Output"), Comma, Esc,
            F.Id("F"), Colon, Sp, F.Id("State"), Sp, To, Sp, F.Id("State"),
            Comma, Sp, F.Id("q"), Colon, Sp, F.Id("State"), Sp, To, Sp,
            F.Id("Output"), Comma, Esc,
            Forall, Sp, y, Comma, Sp, yPrime, Comma, Sp,
            t, InMacro, Mathbb, Grp(F.Id("N")), Comma, Esc,
            Iterate(t, y), Sp, Eq, Sp, Iterate(t, yPrime), Sp,
            Rightarrow, Sp,
            Forall, Sp, r, InMacro, Mathbb, Grp(F.Id("N")), Comma, Esc,
            Open, futureY, Sp, Eq, Sp, futureYPrime, Sp, Land, Sp,
            Read(futureY), Sp, Eq, Sp, Read(futureYPrime), Close, Dot));
    }
}
