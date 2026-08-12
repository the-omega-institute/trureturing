using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms;

internal sealed class GoldenPrimeClassificationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("Golden prime splitting, inertia, and ramification are classified modulo five.",
        H("Golden Prime Classification"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("quadratic-residue-criterion"),
                DeclarationHandle.Create("D5/S3/PrimeForms/GoldenPrimeClassification.five_is_square_mod_prime_iff_mod_five_eq_one_or_four"),
                H("Quadratic-residue criterion"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, F.Id("p"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    Operatorname, Grp(F.Id("Prime")), Open, F.Id("p"), Close, Sp, Land, Sp, F.Id("p"), Neq, D(5), Sp, Land, Sp, F.Id("p"), Neq, D(2), Sp, Rightarrow, Sp,
                    Open, Operatorname, Grp(F.Id("IsSquare")), Open, D(5), Sp, Colon, Sp, Operatorname, Grp(F.Id("ZMod")), Sp, F.Id("p"), Close, Sp, Leftrightarrow, Sp,
                    F.Id("p"), Equiv, Pm, D(1), Esc, Open, Operatorname, Grp(F.Id("mod")), Sp, D(5), Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every odd natural prime p other than five, five is a square modulo p exactly when p is congruent to plus or minus one modulo five. The oddness premise is explicit because the equivalence fails at p = 2."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("split-prime-criterion"),
                DeclarationHandle.Create("D5/S3/PrimeForms/GoldenPrimeClassification.golden_not_prime_iff_mod_five_eq_one_or_four"),
                H("Split-prime criterion"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, F.Id("p"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    Operatorname, Grp(F.Id("Prime")), Open, F.Id("p"), Close, Sp, Land, Sp, F.Id("p"), Neq, D(5), Sp, Rightarrow, Sp,
                    Open, Neg, Operatorname, Grp(F.Id("Prime")), Open, F.Id("p"), Sp, Colon, Sp, Operatorname, Grp(F.Id("GoldenInt")), Close, Sp, Leftrightarrow, Sp,
                    F.Id("p"), Equiv, Pm, D(1), Esc, Open, Operatorname, Grp(F.Id("mod")), Sp, D(5), Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural prime other than five, failure to remain prime in GoldenInt is equivalent to congruence plus or minus one modulo five."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("inert-prime-criterion"),
                DeclarationHandle.Create("D5/S3/PrimeForms/GoldenPrimeClassification.golden_prime_iff_mod_five_eq_two_or_three"),
                H("Inert-prime criterion"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, F.Id("p"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    Operatorname, Grp(F.Id("Prime")), Open, F.Id("p"), Close, Sp, Land, Sp, F.Id("p"), Neq, D(5), Sp, Rightarrow, Sp,
                    Open, Operatorname, Grp(F.Id("Prime")), Open, F.Id("p"), Sp, Colon, Sp, Operatorname, Grp(F.Id("GoldenInt")), Close, Sp, Leftrightarrow, Sp,
                    Open, F.Id("p"), Equiv, D(2), Sp, Lor, Sp, F.Id("p"), Equiv, D(3), Close, Esc, Open, Operatorname, Grp(F.Id("mod")), Sp, D(5), Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural prime other than five, remaining prime in GoldenInt is equivalent to congruence two or three modulo five, namely plus or minus two."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("five-is-a-ramified-square"),
                DeclarationHandle.Create("D5/S3/PrimeForms/GoldenPrimeClassification.golden_five_eq_ramified_square"),
                H("Five is a ramified square"),
                StatementSource.FromAuthor(Disp(Seq(D(5), Sp, Eq, Sp, Open, Minus, D(1), Plus, D(2), Varphi, Close, Caret, D(2)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("In GoldenInt, five is exactly the square of the ramifying element -1 + 2 phi."))),
                DescribeRole.Theorem))));
}
