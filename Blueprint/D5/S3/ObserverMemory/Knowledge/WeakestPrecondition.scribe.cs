using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Knowledge;

internal sealed class WeakestPreconditionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weakest preconditions are inverse images and have the largest guaranteeing domain.",
        H("Weakest Preconditions"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("weakest-precondition-largest-domain"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Knowledge/WeakestPrecondition.wp_minimal"),
                H("Weakest preconditions characterize every guaranteeing domain"),
                StatementSource.FromAuthor(WeakestFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a process F and target set Q, wp_F(Q) is defined as the inverse "
                            + "image of Q. A predicate P guarantees Q after F exactly when P is "
                            + "contained in this inverse image.")),
                    Paragraph(Text(
                        "The second clause quantifies over every other guaranteeing set R and "
                            + "places it inside wp_F(Q). This is the precise largest-domain, hence "
                            + "logically weakest, part of the source claim.")),
                    Paragraph(Text(
                        "Repository searches found no weakest-precondition declaration. Pinned "
                            + "Mathlib's Set.mapsTo_iff_subset_preimage is the exact pointwise "
                            + "characterization and is applied by the proof; Mathlib does not "
                            + "package the additional largest-domain clause."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Wp(Formula process, Formula postcondition) => Seq(
        Operatorname, Grp(F.Id("wp")), Underscore, Grp(process),
        Open, postcondition, Close);

    private static Formula WeakestFormula()
    {
        Formula xType = F.Id("X");
        Formula yType = F.Id("Y");
        Formula process = F.Id("F");
        Formula precondition = F.Id("P");
        Formula postcondition = F.Id("Q");
        Formula candidate = F.Id("R");
        Formula state = F.Id("x");
        Formula weakest = Wp(process, postcondition);

        Formula guaranteesP = Seq(
            Forall, Sp, state, InMacro, Sp, precondition, Comma, Sp,
            Apply(process, state), InMacro, Sp, postcondition);
        Formula guaranteesR = Seq(
            Forall, Sp, state, InMacro, Sp, candidate, Comma, Sp,
            Apply(process, state), InMacro, Sp, postcondition);

        return Disp(Seq(
            Forall, Sp, xType, Comma, Sp, yType, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Esc,
            process, Colon, Sp, xType, Sp, To, Sp, yType, Comma, Esc,
            precondition, Sp, Subseteq, Sp, xType, Comma, Sp,
            postcondition, Sp, Subseteq, Sp, yType, Comma, Esc,
            Open, Grp(guaranteesP), Sp, Iff, Sp,
            precondition, Sp, Subseteq, Sp, weakest, Close, Sp, Land, RowBreak,
            Open, Forall, Sp, candidate, Sp, Subseteq, Sp, xType, Comma, Sp,
            Grp(guaranteesR), Sp, Rightarrow, Sp,
            candidate, Sp, Subseteq, Sp, weakest, Close, Dot));
    }
}
