using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.History;

internal sealed class ReferencedReversalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer ledgers admit exact, explicitly referenced reversal events.",
        H("Referenced Reversal Events"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("group-ledger-reversal-specification"),
                DeclarationHandle.Create("D5/S0/History/ReferencedReversal.group_ledger_reversal_spec"),
                H("Group-ledger reversals cancel and record every negative coordinate"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("Bijective")), Open, F.Id("code"), Close,
                    Sp, Land, Sp,
                    Forall, Sp, F.Id("u"), Comma, Sp,
                    F.Id("code"), Open, Minus, F.Id("u"), Close, Eq,
                    F.Id("delta"), Open, F.Id("rev"), Open, F.Id("u"), Close, Close,
                    Sp, Land, Sp,
                    F.Id("code"), Open, F.Id("u"), Close, Plus,
                    F.Id("delta"), Open, F.Id("rev"), Open, F.Id("u"), Close, Close,
                    Eq, D(0), Sp, Land, Sp,
                    Operatorname, Grp(F.Id("supp")), Open,
                    F.Id("delta"), Open, F.Id("rev"), Open, F.Id("u"), Close, Close,
                    Close, Eq, Operatorname, Grp(F.Id("supp")), Open,
                    F.Id("code"), Open, F.Id("u"), Close, Close,
                    Sp, Land, Sp,
                    Forall, Sp, F.Id("a"), Comma, Sp,
                    F.Id("refs"), Open, F.Id("rev"), Open, F.Id("u"), Close,
                    Comma, F.Id("a"), Close, Neq, Emptyset, Sp, Leftrightarrow, Sp,
                    F.Id("delta"), Open, F.Id("rev"), Open, F.Id("u"), Close,
                    Close, Open, F.Id("a"), Close, Lt, D(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The group-completed ledger on any address type is represented by "
                        + "finitely supported integer coordinates. Given a reference for "
                        + "each address, reversal negates every coordinate. The reversed "
                        + "entry cancels the original exactly and has the same finite "
                        + "support, while its reference set is nonempty exactly where the "
                        + "reversal coordinate is negative. Thus a negative entry cannot "
                        + "occur without an explicit reference to the item being reversed.")),
                    Paragraph(Text(
                        "The library was searched before proving. Pinned Mathlib already "
                        + "identifies the free abelian group on an address type with its "
                        + "finitely supported integer-valued functions through "
                        + "`FreeAbelianGroup.equivFinsupp`, and supplies support preservation "
                        + "under negation through `Finsupp.support_neg`. The Lean theorem is "
                        + "a thin wrapper around that algebraic core plus the repository's "
                        + "small referenced-event structure. Mathlib contains no event type "
                        + "that requires audit references on negative coordinates; that "
                        + "field is the source atom's additional content."))),
                DescribeRole.Theorem))));
}
