using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Eigenstructure;

internal sealed class ReciprocalBalanceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reciprocal antisymmetry forces balance at every negative-norm metallic root.",
        H("Reciprocal Balance"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("metallic-reciprocal-symmetry-forces-balance"),
                DeclarationHandle.Create(
                    "D5/S1/Eigenstructure/ReciprocalBalance."
                    + "metallic_reciprocal_symmetry_forces_balance"),
                H("Reciprocal symmetry forces metallic balance"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("n"), InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    F.Id("s"), Colon, Sp, Mathbb, Grp(F.Id("R")), Sp, To, Sp,
                    Mathbb, Grp(F.Id("R")), Comma, Sp,
                    Open, Forall, Sp, F.Id("x"), InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
                    F.Id("s"), Open, F.Id("x"), Plus, D(1), Close, Eq,
                    F.Id("s"), Open, F.Id("x"), Close, Close, Sp, Land, Sp,
                    F.Id("s"), Open,
                    Frac, Grp(D(1)), Grp(F.Id("m"), Underscore, Grp(F.Id("n"))), Close,
                    Eq, Minus, F.Id("s"), Open,
                    F.Id("m"), Underscore, Grp(F.Id("n")), Close, Sp, Rightarrow, Sp,
                    F.Id("s"), Open, F.Id("m"), Underscore, Grp(F.Id("n")), Close,
                    Eq, D(0), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Here m_n is the positive metallic root "
                        + "(n + sqrt(n^2 + 4))/2. Its frozen reciprocal identity is "
                        + "1/m_n = m_n - n. Unit periodicity identifies the slope at those "
                        + "two arguments, while reciprocal antisymmetry identifies the same "
                        + "value with its negative; characteristic zero then forces zero.")),
                    Paragraph(Text(
                        "The proof directly reuses the repository theorem metallic_family_value "
                        + "and Mathlib's Periodic.sub_nat_mul_eq and CharZero.eq_neg_self_iff. "
                        + "No reciprocal identity, periodic transport law, or characteristic-zero "
                        + "cancellation is reproved here.")),
                    Paragraph(Text(
                        "This is an honest partial closure of only the norm-minus-one balance "
                        + "sentence in source remark 27.135. Existence of the Cesaro-log slope, "
                        + "the reciprocal sign law, the excess formula, the norm-plus-one slope "
                        + "formula, and every numerical certificate remain outside this theorem."))),
                DescribeRole.Theorem))));
}
