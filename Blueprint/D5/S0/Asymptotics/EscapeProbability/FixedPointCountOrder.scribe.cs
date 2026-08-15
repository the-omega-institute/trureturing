using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Asymptotics.EscapeProbability;

internal sealed class FixedPointCountOrderDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive-address frozen escape probability strictly reverses fixed-point-count order.",
        H("Fixed-Point Count Order"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("escape-probability-strictly-orders-fixed-point-counts"),
                DeclarationHandle.Create(
                    "D5/S0/Asymptotics/EscapeProbability/FixedPointCountOrder."
                        + "escape_probability_lt_iff_fixed_point_card_gt"),
                H("Escape probability strictly reverses fixed-point-count order"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("Y"), Comma, Sp,
                    OpenBracket, Operatorname, Grp(F.Id("Fintype")), Sp, F.Id("Y"),
                    CloseBracket, Sp,
                    OpenBracket, Operatorname, Grp(F.Id("Nonempty")), Sp, F.Id("Y"),
                    CloseBracket, Comma, Sp,
                    Forall, Sp, F.Id("f"), Comma, Sp, F.Id("g"), Colon, Sp,
                    F.Id("Y"), Sp, To, Sp, F.Id("Y"), Comma, Sp,
                    Forall, Sp, F.Id("A"), InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    D(0), Sp, Lt, Sp, F.Id("A"), Sp, Rightarrow, Sp,
                    Open,
                    Call("escapeProbability", Call("Fin", F.Id("A")), F.Id("f")),
                    Sp, Lt, Sp,
                    Call("escapeProbability", Call("Fin", F.Id("A")), F.Id("g")),
                    Sp, Iff, Sp,
                    Call("card", Call("Fix", F.Id("g"))), Sp, Lt, Sp,
                    Call("card", Call("Fix", F.Id("f"))),
                    Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For two endomorphisms f and g of the same finite nonempty output "
                            + "alphabet and any positive address count A, the frozen escape "
                            + "probability of f is smaller than that of g exactly when f has "
                            + "strictly more fixed points than g.")),
                    Paragraph(Text(
                        "The proof applies the frozen closed form to both probabilities. The "
                            + "fixed-point subtype bound makes both power bases nonnegative; "
                            + "pinned Mathlib's pow_lt_pow_iff_left₀ removes the positive power, "
                            + "and div_lt_div_iff_of_pos_right compares the fixed-point counts.")),
                    Paragraph(Text(
                        "Repository and all-local-ref searches found no existing comparison "
                            + "theorem. This order characterization is independent of the two "
                            + "endpoint characterizations and does not use the distance-profile "
                            + "or weighted-mass developments."))),
                DescribeRole.Theorem)),
        []));
}
