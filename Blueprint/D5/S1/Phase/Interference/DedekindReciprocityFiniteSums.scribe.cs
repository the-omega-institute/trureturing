using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Phase.Interference;

internal sealed class DedekindReciprocityFiniteSumsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coprime multiplication permutes the nonzero residues and preserves their exact rational sum.",
        H("Finite Residue Sums for Dedekind Reciprocity"),
        Blocks(
            Paragraph(Text(
                "The module first rewrites the frozen rational sawtooth by a natural remainder. "
                    + "It then evaluates the linear and square sums on the interval from one to "
                    + "c minus one and proves the residue permutation with Finset.sum_bij.")),
            Describe.Lean(
                DescribeId.Create("coprime-residue-permutation-sum"),
                DeclarationHandle.Create(
                    "D5/S1/Phase/Interference/DedekindReciprocityFiniteSums.sum_mul_mod"),
                H("Coprime multiplication preserves the nonzero-residue sum"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("d"), Comma, Sp, F.Id("c"), InMacro, Sp,
                    Mathbb, Grp(F.Id("N")), Comma, Esc,
                    F.Id("c"), Gt, D(0), Sp, Land, Sp,
                    Gcd, Open, F.Id("d"), Comma, Sp, F.Id("c"), Close,
                    Eq, D(1), Sp, Rightarrow, Sp,
                    Sum, Underscore, Grp(F.Id("k"), Eq, D(1)),
                    Caret, Grp(F.Id("c"), Minus, D(1)),
                    OpenBracket, Open, F.Id("k"), F.Id("d"), Close,
                    Sp, Operatorname, Grp(F.Id("mod")), Sp, F.Id("c"), CloseBracket,
                    Underscore, Grp(Mathbb, Grp(F.Id("Q"))),
                    Sp, Eq, Sp,
                    Frac,
                    Grp(F.Id("c"), Open, F.Id("c"), Minus, D(1), Close),
                    Grp(D(2)), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The supporting named results are sawtooth_div_eq_mod, "
                        + "dedekindSum_eq_mod_sum, sum_Ico_cast, sum_Ico_cast_sq, "
                        + "sum_mul_mod_permutation, and sum_mul_mod_sq."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S1/Phase/Interference/DedekindBhkCertificates")),
        ]));
}
