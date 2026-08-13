using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Asymptotics;

internal sealed class NameSetDistanceSandwichDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Distances to three nested nonempty name sets form a reversed sandwich.",
        H("Name-Set Distance Sandwich"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nested-name-sets-give-a-distance-sandwich"),
                DeclarationHandle.Create(
                    "D5/S0/Asymptotics/NameSetDistanceSandwich.nested_name_set_infDist_sandwich"),
                H("Nested name sets give a reversed distance sandwich"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, Alpha, Comma, Sp,
                    OpenBracket, Operatorname, Grp(F.Id("PseudoMetricSpace")), Open, Alpha, Close,
                    CloseBracket, Comma, Esc,
                    Forall, Sp, F.Id("x"), InMacro, Alpha, Comma, Sp,
                    Forall, Sp, F.Id("P"), Comma, F.Id("T"), Comma, F.Id("K"),
                    Subseteq, Alpha, Comma, Esc,
                    F.Id("P"), Sp, Subseteq, Sp, F.Id("T"), Sp, Land, Sp,
                    F.Id("T"), Sp, Subseteq, Sp, F.Id("K"), Sp, Land, Sp,
                    Operatorname, Grp(F.Id("Nonempty")), Open, F.Id("P"), Close,
                    Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("infDist")), Open, F.Id("x"), Comma, F.Id("P"), Close,
                    Sp, Ge, Sp,
                    Operatorname, Grp(F.Id("infDist")), Open, F.Id("x"), Comma, F.Id("T"), Close,
                    Sp, Land, Sp,
                    Operatorname, Grp(F.Id("infDist")), Open, F.Id("x"), Comma, F.Id("T"), Close,
                    Sp, Ge, Sp,
                    Operatorname, Grp(F.Id("infDist")), Open, F.Id("x"), Comma, F.Id("K"), Close,
                    Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "After the two additive budget shifts are absorbed into the supplied level "
                        + "sets P, T, and K, the source's metric conclusion follows from the two "
                        + "inclusions P subset T and T subset K. The Lean proof invokes Mathlib's "
                        + "infDist_le_infDist_of_subset once for each inclusion.")),
                    Paragraph(Text(
                        "The nonemptiness premise is necessary for real-valued infDist: Mathlib "
                        + "defines the distance to the empty set as zero. Nonemptiness of T follows "
                        + "from that of P and the first inclusion.")),
                    Paragraph(Text(
                        "This deposit partially closes only the nested-distance consequence in "
                        + "clause (a) of source theorem 6.5. It does not construct the prefix-to-test "
                        + "or test-to-program coding embeddings, prove their additive overhead "
                        + "bounds, or close either separation family in clause (b); all of those "
                        + "subitems remain unresolved."))),
                DescribeRole.Theorem))));
}
