using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.GovernanceFixedPoint;

internal sealed class TailRekeyExistenceDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/GovernanceFixedPoint/TailRekeyExistence.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every eligible active tail has a legal rekey along a document prefix extension.",
        H("Legal Tail Rekey Existence"),
        Blocks(Describe.Lean(
            DescribeId.Create("legal-tail-rekey-exists"),
            DeclarationHandle.Create(Prefix + "legal_tail_rekey_exists"),
            H("Legal tail rekeys exist"),
            StatementSource.FromAuthor(LegalTailRekeyFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The replacement keeps the logical identifier and settlement, records "
                        + "the old content key as predecessor, and updates only the active "
                        + "key selected by that identifier.")),
                Paragraph(Text(
                    "The document prefix extension supplies the replacement tail's prefix "
                        + "clause through the tail-span preservation theorem."))),
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

    private static Formula Field(Formula value, string field) =>
        Seq(value, Dot, F.Id(field));

    private static Formula LegalTailRekeyFormula()
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
                Apply(tailEligible, Field(oldEntry, "logicalId")), Sp, Land, Sp,
                Apply(F.Id("PrefixExtension"), oldDocument, newDocument), Sp, Land, Sp),
            Seq(
                start, Sp, Le, Sp, Field(oldDocument, "length"), Sp, Land, Sp,
                Field(oldEntry, "bytes"), Sp, Eq, Sp,
                Apply(F.Id("TailBytes"), oldDocument, start), Sp, Land, Sp),
            Seq(
                Apply(
                    F.Id("ActiveSource"), active,
                    Field(oldEntry, "logicalId"), Field(oldEntry, "key")), Sp,
                Rightarrow, Sp),
            Seq(
                Exists, Sp,
                Typed(result, Apply(F.Id("RekeyResult"), idType, byteType)), Comma, Sp,
                Apply(
                    F.Id("LegalTailRekey"), tailEligible,
                    oldDocument, newDocument, start,
                    oldEntry, active, settlement, result),
                Dot),
        ]));
    }
}
