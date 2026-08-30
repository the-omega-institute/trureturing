using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.GovernanceFixedPoint;

internal sealed class TailSpanPrefixExtensionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/GovernanceFixedPoint/TailSpanPrefixExtension.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A tail span preserves a document prefix extension when its start lies in the old "
            + "document.",
        H("Tail Span Prefix Extension"),
        Blocks(Describe.Lean(
            DescribeId.Create("tail-span-prefix-extension"),
            DeclarationHandle.Create(Prefix + "tail_span_prefix_extension"),
            H("Tail spans preserve prefix extension"),
            StatementSource.FromAuthor(TailSpanPrefixFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A source suffix remains after dropping any offset contained in the old "
                        + "document.")),
                Paragraph(Text(
                    "Thus the old tail is still an exact prefix of the extended document's "
                        + "tail, with the original suffix as witness."))),
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

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Field(Formula value, string field) =>
        Seq(value, Dot, F.Id(field));

    private static Formula TailSpanPrefixFormula()
    {
        Formula byteType = F.Id("Byte");
        Formula oldDocument = F.Id("oldDocument");
        Formula newDocument = F.Id("newDocument");
        Formula start = F.Id("start");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula listType = Apply(F.Id("List"), byteType);

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, Typed(byteType, type), Comma),
            Seq(
                Forall, Sp,
                Typed(Seq(oldDocument, Comma, Sp, newDocument), listType), Comma),
            Seq(Forall, Sp, Typed(start, F.Id("Nat")), Comma),
            Seq(
                Apply(F.Id("PrefixExtension"), oldDocument, newDocument), Sp,
                Land, Sp, start, Sp, Le, Sp, Field(oldDocument, "length"), Sp,
                Rightarrow, Sp),
            Seq(
                Apply(
                    F.Id("PrefixExtension"),
                    Apply(F.Id("TailBytes"), oldDocument, start),
                    Apply(F.Id("TailBytes"), newDocument, start)),
                Dot),
        ]));
    }
}
