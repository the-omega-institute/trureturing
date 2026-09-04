using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaLinear;

internal sealed class FullRankInertiaPullbackDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/ZetaLinear/FullRankInertiaPullback.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hermitian pullback cannot increase negative index, and an explicit right inverse preserves the full positive-negative inertia pair exactly.",
        H("Full-Rank Inertia Pullback"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("negative-index-cannot-increase-under-pullback"),
                DeclarationHandle.Create(Prefix + "negIndex_conj_le"),
                H("Negative index cannot increase under pullback"),
                StatementSource.FromAuthor(NegativePullbackFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The repository already owns the positive-index pullback inequality. The new theorem proves the negative companion through the frozen Hermitian negative-part calculus and the same finite-dimensional image argument."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("right-inverse-preserves-positive-index"),
                DeclarationHandle.Create(Prefix + "posIndex_conj_eq_of_rightInverse"),
                H("A right inverse preserves positive index"),
                StatementSource.FromAuthor(PositiveRightInverseFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The forward inequality is the frozen pullback theorem. The explicit right inverse pulls the pulled-back form back to the original form and supplies the reverse inequality."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("right-inverse-preserves-negative-index"),
                DeclarationHandle.Create(Prefix + "negIndex_conj_eq_of_rightInverse"),
                H("A right inverse preserves negative index"),
                StatementSource.FromAuthor(NegativeRightInverseFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The same two-sided pullback argument preserves the number of strictly negative eigenvalues exactly."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("right-inverse-preserves-the-full-inertia-pair"),
                DeclarationHandle.Create(Prefix + "inertia_conj_eq_of_rightInverse"),
                H("A right inverse preserves the full inertia pair"),
                StatementSource.FromAuthor(FullInertiaFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The result packages positive- and negative-index preservation. It is the reusable algebraic certificate required by rectangular full-rank Cauchy and Vandermonde feature maps."))),
                DescribeRole.Theorem)),
        []));

    private static Formula Pullback(Formula b, Formula q) =>
        Call("pullback", b, q);

    private static Formula NegativePullbackFormula()
    {
        var b = F.Id("B");
        var q = F.Id("Q");
        return Disp(Seq(
            Call("negIndex", Pullback(b, q)), Sp, Leq, Sp,
            Call("negIndex", q), Dot));
    }

    private static Formula PositiveRightInverseFormula()
    {
        var b = F.Id("B");
        var r = F.Id("R");
        var q = F.Id("Q");
        return Disp(Seq(
            Equal(Multiply(b, r), F.Id("I")), Sp, Rightarrow, Sp,
            Equal(Call("posIndex", Pullback(b, q)), Call("posIndex", q)), Dot));
    }

    private static Formula NegativeRightInverseFormula()
    {
        var b = F.Id("B");
        var r = F.Id("R");
        var q = F.Id("Q");
        return Disp(Seq(
            Equal(Multiply(b, r), F.Id("I")), Sp, Rightarrow, Sp,
            Equal(Call("negIndex", Pullback(b, q)), Call("negIndex", q)), Dot));
    }

    private static Formula FullInertiaFormula()
    {
        var b = F.Id("B");
        var r = F.Id("R");
        var q = F.Id("Q");
        return Disp(Seq(
            Equal(Multiply(b, r), F.Id("I")), Sp, Rightarrow, Sp,
            Open,
            Equal(Call("posIndex", Pullback(b, q)), Call("posIndex", q)),
            Sp, Land, Sp,
            Equal(Call("negIndex", Pullback(b, q)), Call("negIndex", q)),
            Close, Dot));
    }
}
