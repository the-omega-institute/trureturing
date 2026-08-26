using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics;

internal sealed class CodeLedgerIdentityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("A canonical prime-axis code together with a ledger coordinate exactly determines state identity.",
        H("Identity from Canonical Code and Ledger"),
        Blocks(
            Describe.Lean(DescribeId.Create("same-state-iff-same-code-and-ledger"),
                DeclarationHandle.Create(
                                    "D5/S1/Dynamics/CodeLedgerIdentity."
                                    + "same_state_iff_same_code_and_ledger"),
                H("States agree exactly when their codes and ledgers agree"),
                StatementSource.FromAuthor(Disp(Seq(
                                    Forall, Sp, F.Id("Ledger"), Colon, Sp,
                                    Operatorname, Grp(F.Id("Type")), Comma, Sp,
                                    Forall, Sp, F.Id("K"), Underscore, D(1), Comma, Sp,
                                    F.Id("K"), Underscore, D(2), Colon, Sp,
                                    Operatorname, Grp(F.Id("CodeLedgerState")), Open,
                                    F.Id("Ledger"), Close, Comma, Sp,
                                    F.Id("K"), Underscore, D(1), Eq, F.Id("K"), Underscore, D(2),
                                    Sp, Iff, Sp,
                                    Operatorname, Grp(F.Id("code")), Open,
                                    F.Id("K"), Underscore, D(1), Close,
                                    Eq,
                                    Operatorname, Grp(F.Id("code")), Open,
                                    F.Id("K"), Underscore, D(2), Close,
                                    Sp, Land, Sp,
                                    Operatorname, Grp(F.Id("ledger")), Open,
                                    F.Id("K"), Underscore, D(1), Close,
                                    Eq,
                                    Operatorname, Grp(F.Id("ledger")), Open,
                                    F.Id("K"), Underscore, D(2), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "A state pairs a canonical prime-axis coordinate with an arbitrary "
                                        + "ledger coordinate. Its code is the positive-natural value supplied "
                                        + "by the existing prime-axis encoding equivalence. Equality of states "
                                        + "therefore has exactly two observable requirements: equality of the "
                                        + "canonical codes and equality of the ledgers. The reverse implication "
                                        + "uses injectivity of the canonical encoding, so it does not assume the "
                                        + "identity criterion as a premise.")),
                                    Paragraph(Text(
                                        "The pinned library was searched first for equivalence injectivity and "
                                        + "product extensionality. It supplies Equiv.apply_eq_iff_eq, "
                                        + "Equiv.injective, and Prod.ext_iff, but no theorem combining the "
                                        + "repository's canonical prime-axis code with a ledger. The formal "
                                        + "declaration is consequently a new repository-local composition of "
                                        + "the existing encoding equivalence with generated structure "
                                        + "constructor injectivity, matching the single criterion in the "
                                        + "source atom."))),
                DescribeRole.Theorem))));
}
