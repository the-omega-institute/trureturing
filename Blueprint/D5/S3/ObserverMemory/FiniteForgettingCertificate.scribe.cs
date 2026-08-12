using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory;

internal sealed class FiniteForgettingCertificateDocument : IScribeDocumentDefinition
{
    private const string LeanPrefix = "D5/S3/ObserverMemory/FiniteForgettingCertificate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("Finite forgetting and recall histories preserve irreversible ledger marks and incompatible-claim separation.",
        H("Named Cognitive-State Forgetting Certificate"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("the-cognitive-alphabet-has-six-named-states"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/FiniteForgettingCertificate.cognitive_state_card"),
                H("The cognitive alphabet has six named states"),
                StatementSource.FromAuthor(CardFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The inductive alphabet consists exactly of Remember, NeverKnown, Forgotten, "
                    + "Misremember, Recall, and AccessRevoked. These are semantic constructors, "
                    + "not points of a coordinate product. The count supports the certificate but "
                    + "does not serve as its principal invariant."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("remember-forget-recall-is-a-nonempty-certified-history"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/FiniteForgettingCertificate.remember_forget_recall_certificate"),
                H("Remember-forget-recall is a nonempty certified history"),
                StatementSource.FromAuthor(ConcreteHistoryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A concrete coherent Remember certificate executes Forget and then Recall as "
                    + "two distinct admitted transitions through Forgotten. The final Recall "
                    + "certificate still carries forgottenLogged and cannot simultaneously carry "
                    + "an open Misremember claim. This supplies an occupied, non-reflexive history "
                    + "rather than relying on the reflexive case of finite closure."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("access-revocation-is-terminal"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/FiniteForgettingCertificate.access_revoked_terminal"),
                H("Access revocation is terminal"),
                StatementSource.FromAuthor(TerminalFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "AccessRevoked has no outgoing admitted action. Its certificate carries a typed "
                    + "revocation reason; this reason-bearing entry separates administrative loss "
                    + "of access from epistemic Forgotten and cannot be silently rewritten."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("misremember-cannot-jump-directly-to-recall"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/FiniteForgettingCertificate.misremember_cannot_recall_directly"),
                H("Misremember cannot jump directly to Recall"),
                StatementSource.FromAuthor(IncompatibleArcFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A false-memory claim must first be retracted to Forgotten. The dynamics has "
                    + "no direct Misremember-to-Recall arc, preventing a single transition from "
                    + "treating incompatible false and accurate claims as interchangeable."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-histories-preserve-the-certificate-invariants"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/FiniteForgettingCertificate.finite_history_certificate"),
                H("Finite histories preserve the certificate invariants"),
                StatementSource.FromAuthor(HistoryCertificateFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every coherent source and every finite chain of admitted transitions, the "
                    + "target remains coherent. A prior Forgotten mark stays set; a prior "
                    + "reason-bearing AccessRevoked entry keeps the same reason; and the target "
                    + "cannot carry simultaneous active Misremember and Recall claims. This closure "
                    + "and monotonicity result is the certificate's principal theorem."))),
                DescribeRole.Theorem))));

    private static Formula CardFormula() => Disp(Seq(
        Operatorname, Grp(F.Id("card")), Open, F.Id("CognitiveState"), Close,
        Eq, F.D(6), Dot));

    private static Formula ConcreteHistoryFormula() => Disp(Seq(
        Operatorname, Grp(F.Id("Coherent")), Open, F.Id("r0"), Close,
        Sp, Land, Sp,
        Operatorname, Grp(F.Id("FiniteHistory")), Open,
        F.Id("r0"), Comma, F.Id("r2"), Close,
        Sp, Land, RowBreak,
        Operatorname, Grp(F.Id("ForgottenLogged")), Open, F.Id("r2"), Close,
        Sp, Land, Sp,
        Neg, Open,
        Operatorname, Grp(F.Id("MisrememberOpen")), Open, F.Id("r2"), Close,
        Sp, Land, Sp,
        Operatorname, Grp(F.Id("RecallOpen")), Open, F.Id("r2"), Close,
        Close, Dot));

    private static Formula TerminalFormula() => Disp(Seq(
        Forall, Sp, F.Id("s"), Comma, F.Id("t"), Comma, Esc,
        Operatorname, Grp(F.Id("state")), Open, F.Id("s"), Close,
        Eq, Mathrm, Grp(F.Id("AccessRevoked")), Sp, Rightarrow, Sp,
        Neg, Operatorname, Grp(F.Id("Transition")), Open,
        F.Id("s"), Comma, F.Id("t"), Close, Dot));

    private static Formula IncompatibleArcFormula() => Disp(Seq(
        Forall, Sp, F.Id("s"), Comma, F.Id("t"), Comma, Esc,
        Open,
        Operatorname, Grp(F.Id("state")), Open, F.Id("s"), Close,
        Eq, Mathrm, Grp(F.Id("Misremember")), Sp, Land, Sp,
        Operatorname, Grp(F.Id("state")), Open, F.Id("t"), Close,
        Eq, Mathrm, Grp(F.Id("Recall")), Close, Sp, Rightarrow, Sp,
        Neg, Operatorname, Grp(F.Id("Transition")), Open,
        F.Id("s"), Comma, F.Id("t"), Close, Dot));

    private static Formula HistoryCertificateFormula() => Disp(Seq(
        Forall, Sp, F.Id("s"), Comma, F.Id("t"), Comma, Esc,
        Open,
        Operatorname, Grp(F.Id("Coherent")), Open, F.Id("s"), Close,
        Sp, Land, Sp,
        Operatorname, Grp(F.Id("FiniteHistory")), Open,
        F.Id("s"), Comma, F.Id("t"), Close,
        Close, Sp, Rightarrow, RowBreak,
        Operatorname, Grp(F.Id("Coherent")), Open, F.Id("t"), Close,
        Sp, Land, Sp,
        Open,
        Operatorname, Grp(F.Id("ForgottenLogged")), Open, F.Id("s"), Close,
        Sp, Rightarrow, Sp,
        Operatorname, Grp(F.Id("ForgottenLogged")), Open, F.Id("t"), Close,
        Close, Sp, Land, RowBreak,
        Open,
        Operatorname, Grp(F.Id("RevokedLogged")), Open, F.Id("s"), Close,
        Sp, Rightarrow, Sp,
        Operatorname, Grp(F.Id("reason")), Open, F.Id("t"), Close,
        Eq, Operatorname, Grp(F.Id("reason")), Open, F.Id("s"), Close,
        Close, Sp, Land, RowBreak,
        Neg, Open,
        Operatorname, Grp(F.Id("MisrememberOpen")), Open, F.Id("t"), Close,
        Sp, Land, Sp,
        Operatorname, Grp(F.Id("RecallOpen")), Open, F.Id("t"), Close,
        Close, Dot));
}
