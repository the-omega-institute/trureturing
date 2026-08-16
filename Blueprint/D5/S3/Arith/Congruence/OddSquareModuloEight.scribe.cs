using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class OddSquareModuloEightDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every odd natural number has square congruent to one modulo eight.",
        H("Odd Squares Modulo Eight"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("eight-divides-odd-square-minus-one"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Congruence/OddSquareModuloEight.eight_dvd_odd_square_sub_one"),
                H("Eight divides an odd square minus one"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("T"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    Operatorname, Grp(F.Id("Odd")), Open, F.Id("T"), Close, Sp,
                    Rightarrow, Sp, D(8), Sp, Mid, Sp,
                    F.Id("T"), Caret, Grp(D(2)), Sp, Minus, Sp, D(1)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "If T is odd, its square differs from one by a multiple of eight. "
                        + "Pinned Mathlib supplies the exact theorem "
                        + "Nat.eight_dvd_sq_sub_one_of_odd, so the Lean declaration is a thin "
                        + "wrapper rather than a second proof of the parity argument.")),
                    Paragraph(Text(
                        "This closes only the explicit divisibility clause in residual appendix E.115. "
                        + "It does not formalize the eta-multiplier branch formulas or the subsequent "
                        + "context-dependent assertion that quantities A and C are even."))),
                DescribeRole.Theorem
            )),
        []));
}
