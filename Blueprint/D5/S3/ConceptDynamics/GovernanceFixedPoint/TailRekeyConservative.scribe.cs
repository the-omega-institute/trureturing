using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.GovernanceFixedPoint;

internal sealed class TailRekeyConservativeDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/GovernanceFixedPoint/TailRekeyConservative.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every legal tail rekey preserves settlement and changes only its active source.",
        H("Legal Tail Rekey Conservativity"),
        Blocks(Describe.Lean(
            DescribeId.Create("legal-tail-rekey-is-conservative"),
            DeclarationHandle.Create(Prefix + "legal_tail_rekey_is_conservative"),
            H("Legal tail rekeys are conservative"),
            StatementSource.FromAuthor(ConservativityFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "The named conservativity predicate records the old predecessor and stable "
                    + "logical identifier, equality of the complete settlement view, the "
                    + "unique active key at the target identifier, and preservation of every "
                    + "other identifier's active key."))),
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

    private static Formula ConservativityFormula()
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
        Formula result = F.Id("result");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula listType = Apply(F.Id("List"), byteType);

        Formula legal = Apply(
            F.Id("LegalTailRekey"), tailEligible,
            oldDocument, newDocument, start,
            oldEntry, active, settlement, result);
        Formula conservative = Apply(
            F.Id("ConservativeRekey"), active, settlement, oldEntry, result);

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
                Typed(result, Apply(F.Id("RekeyResult"), idType, byteType)), Comma, RowBreak, Grp()),
            Seq(legal, Sp, Rightarrow, RowBreak, Grp(), conservative, Dot),
        ]));
    }
}
