using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Audits;

internal sealed class LedgerIntegrityVeracitySeparationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An injective ledger can exactly preserve reports that systematically contradict events.",
        H("Ledger Integrity and Input Veracity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("ledger-integrity-does-not-imply-input-veracity"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Audits/LedgerIntegrityVeracitySeparation."
                        + "ledger_integrity_does_not_imply_input_veracity"),
                H("Ledger integrity does not imply input veracity"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Take Boolean events. The true-event readout is the identity, while the "
                            + "report readout negates every event. The encoder is the identity and "
                            + "the ledger is constructed as the encoder composed with the report.")),
                    Paragraph(Text(
                        "The induced ledger distinguishes two inputs exactly when their reports "
                            + "differ. Boolean negation is injective, but every report is unequal to "
                            + "the corresponding true event.")),
                    Paragraph(Text(
                        "All five clauses are public: encoder injectivity, exact report distinction, "
                            + "systematic report/event inequality, ledger injectivity, and the failure "
                            + "of ledger integrity to have the same truth value as input veracity.")),
                    Paragraph(Text(
                        "Repository searches found no exact combined theorem. The proof directly "
                            + "applies the pinned Boolean injectivity and inequality theorems."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula Compose(Formula left, Formula right) =>
        Seq(left, Sp, Circ, Sp, right);

    private static Formula TheoremFormula()
    {
        Formula boolean = F.Id("Bool");
        Formula booleanMap = Arrow(boolean, boolean);
        Formula trueEvent = F.Id("O");
        Formula report = F.Id("R");
        Formula encode = F.Id("E");
        Formula ledger = F.Id("L");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula exactDistinction = Seq(
            Forall, Sp, x, Comma, Sp, y, InMacro, Sp, boolean, Comma, Sp,
            Open,
            Apply(ledger, x), Sp, Neq, Sp, Apply(ledger, y), Sp, Iff, Sp,
            Apply(report, x), Sp, Neq, Sp, Apply(report, y),
            Close);
        Formula systematicallyFalse = Seq(
            Forall, Sp, x, InMacro, Sp, boolean, Comma, Sp,
            Apply(report, x), Sp, Neq, Sp, Apply(trueEvent, x));
        Formula integrityDiffersFromVeracity = Seq(
            Neg, Sp, Open,
            Call("Injective", ledger), Sp, Iff, Sp,
            report, Sp, Eq, Sp, trueEvent,
            Close);

        return Disp(Seq(
            Exists, Sp, trueEvent, Comma, Sp, report, Comma, Sp, encode,
            Colon, Sp, booleanMap, Comma, RowBreak, Grp(),
            ledger, Sp, Colon, Eq, Sp, Compose(encode, report), Comma, RowBreak, Grp(),
            Call("Injective", encode), Sp, Land, RowBreak, Grp(),
            Grp(exactDistinction), Sp, Land, RowBreak, Grp(),
            Grp(systematicallyFalse), Sp, Land, RowBreak, Grp(),
            Call("Injective", ledger), Sp, Land, RowBreak, Grp(),
            integrityDiffersFromVeracity, Dot));
    }
}
