using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.GovernanceFixedPoint;

internal sealed class TailRekeyUniquenessDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/GovernanceFixedPoint/TailRekeyUniqueness.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A legal tail rekey is uniquely determined by its document and ledger inputs.",
        H("Legal Tail Rekey Uniqueness"),
        Blocks(Describe.Lean(
            DescribeId.Create("legal-tail-rekey-unique"),
            DeclarationHandle.Create(Prefix + "legal_tail_rekey_unique"),
            H("Legal tail rekeys are unique"),
            StatementSource.FromAuthor(UniquenessFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "Legality fixes the predecessor, replacement entry, active-index update, "
                    + "and settlement view. Structure and function extensionality therefore "
                    + "identify any two legal results without a hash assumption."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Legal(
        Formula tailEligible,
        Formula oldDocument,
        Formula newDocument,
        Formula start,
        Formula oldEntry,
        Formula active,
        Formula settlement,
        Formula result) =>
        Apply(
            F.Id("LegalTailRekey"), tailEligible,
            oldDocument, newDocument, start,
            oldEntry, active, settlement, result);

    private static Formula UniquenessFormula()
    {
        Formula idType = F.Id("Id");
        Formula byteType = F.Id("Byte");
        Formula tailEligible = F.Id("tailEligible");
        Formula oldDocument = F.Id("oldDocument");
        Formula newDocument = F.Id("newDocument");
        Formula start = F.Id("start");
        Formula oldEntry = F.Id("oldEntry");
        Formula active = F.Id("active");
        Formula settlement = F.Id("settlement");
        Formula first = F.Id("first");
        Formula second = F.Id("second");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula listType = Apply(F.Id("List"), byteType);
        Formula resultType = Apply(F.Id("RekeyResult"), idType, byteType);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp,
                Typed(Seq(idType, Comma, Sp, byteType), type), Comma),
            Seq(
                Grp(), OpenBracket,
                Apply(F.Id("DecidableEq"), idType), CloseBracket, Comma),
            Seq(
                Forall, Sp,
                Typed(tailEligible, Arrow(idType, F.Id("Prop"))), Comma),
            Seq(
                Forall, Sp,
                Typed(Seq(oldDocument, Comma, Sp, newDocument), listType), Comma),
            Seq(Forall, Sp, Typed(start, F.Id("Nat")), Comma),
            Seq(
                Forall, Sp,
                Typed(oldEntry, Apply(F.Id("LedgerEntry"), idType, byteType)), Comma),
            Seq(
                Forall, Sp,
                Typed(active, Apply(F.Id("ActiveIndex"), idType, byteType)), Comma),
            Seq(
                Forall, Sp,
                Typed(settlement, Apply(F.Id("Settlement"), idType)), Comma),
            Seq(
                Forall, Sp,
                Typed(Seq(first, Comma, Sp, second), resultType), Comma, RowBreak, Grp()),
            Seq(
                Open, Legal(
                    tailEligible, oldDocument, newDocument, start,
                    oldEntry, active, settlement, first), Sp, Land, RowBreak, Grp()),
            Seq(
                Legal(
                    tailEligible, oldDocument, newDocument, start,
                    oldEntry, active, settlement, second), Close, Sp, Rightarrow, Sp),
            Seq(first, Sp, Eq, Sp, second, Dot),
        ]));
    }
}
