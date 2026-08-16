using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms.Symmetry;

internal sealed class InversionAntisymmetricSumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An inversion-antisymmetric integer-valued function sums to zero on a finite group.",
        H("Cancellation Under Group Inversion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("inversion-antisymmetric-functions-have-zero-total-sum"),
                DeclarationHandle.Create(
                    "D5/S3/PrimeForms/Symmetry/InversionAntisymmetricSum."
                    + "inversion_antisymmetric_sum_eq_zero"),
                H("Inversion antisymmetry forces total cancellation"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("G"), Sp,
                    Operatorname, Grp(F.Id("finite"), Sp, F.Id("group")), Comma, Esc,
                    Forall, Sp, F.Id("f"), Colon, Sp, F.Id("G"), Sp, To, Sp,
                    Mathbb, Grp(F.Id("Z")), Comma, Esc,
                    Open, Forall, Sp, F.Id("g"), Colon, Sp, F.Id("G"), Comma, Esc,
                    F.Id("f"), Open, F.Id("g"), Caret, Grp(Minus, D(1)), Close,
                    Sp, Eq, Sp, Minus, F.Id("f"), Open, F.Id("g"), Close, Close,
                    Sp, Rightarrow, Sp,
                    Sum, Underscore, Grp(F.Id("g"), InMacro, Sp, F.Id("G")), Sp,
                    F.Id("f"), Open, F.Id("g"), Close, Sp, Eq, Sp, D(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let G be a finite group and let f be integer-valued. If f sends the "
                        + "inverse of every group element to the negative of its value, then the "
                        + "sum of f over G is zero. Distinct inverse pairs cancel, while any "
                        + "self-inverse element has value equal to its own negative and hence "
                        + "has value zero in the integers.")),
                    Paragraph(Text(
                        "The Lean proof is a thin specialization of Mathlib's "
                        + "Finset.sum_ninvolution to inversion on the universal finite set. It "
                        + "also reuses Equiv.inv for the pairing and "
                        + "CharZero.eq_neg_self_iff for fixed points. Repository and pinned-Mathlib "
                        + "searches found no end-to-end theorem for this exact finite-group sum.")),
                    Paragraph(Text(
                        "This closes only the sentence in appendix E.110 stating that inversion "
                        + "changes sign and therefore the total finite-circle sum is zero. It does "
                        + "not assert the negative-continued-fraction bijection, the class-number "
                        + "law, or any other clause of that residual atom."))),
                DescribeRole.Theorem
            )),
        []));
}
