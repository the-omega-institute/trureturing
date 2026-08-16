using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms.Crossing;

internal sealed class OddCoreParameterCriterionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive square root has a unique exchange parameter exactly when twice it divides the gcd.",
        H("Odd-Core Parameter Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("square-and-gcd-determine-the-exchange-parameter"),
                DeclarationHandle.Create(
                    "D5/S3/PrimeForms/Crossing/OddCoreParameterCriterion."
                    + "odd_core_parameter_criterion"),
                H("Square and gcd data determine the exchange parameter"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("m"), Comma, Sp, F.Id("b"), Comma, Sp,
                    F.Id("c"), InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    Left, Open,
                    Exists, Sp, F.Id("x"), InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    F.Id("x"), Caret, Grp(D(2)), Eq, F.Id("m"), Sp, Land, Sp,
                    D(0), Lt, F.Id("x"), Sp, Land, Sp,
                    Exists, Bang, Sp, F.Id("y"), InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    D(2), Times, Sp, F.Id("x"), Times, Sp, F.Id("y"), Eq,
                    Gcd, Open, F.Id("b"), Comma, Sp, F.Id("c"), Close,
                    Right, Close, Sp, Iff, Sp, Left, Open,
                    Exists, Sp, F.Id("x"), InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    F.Id("x"), Caret, Grp(D(2)), Eq, F.Id("m"), Sp, Land, Sp,
                    D(0), Lt, F.Id("x"), Sp, Land, Sp,
                    D(2), Times, Sp, F.Id("x"), Sp, Mid, Sp,
                    Gcd, Open, F.Id("b"), Comma, Sp, F.Id("c"), Close,
                    Right, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix a positive natural square root x of m. A witness for divisibility "
                            + "of gcd(b,c) by 2x is exactly a parameter y satisfying "
                            + "2xy = gcd(b,c). Positivity makes 2x nonzero, so cancellation "
                            + "shows that two such parameters must agree.")),
                    Paragraph(Text(
                        "Repository and pinned-Mathlib searches found no equivalent combined "
                            + "criterion. Loogle found no matching divisibility equivalence or "
                            + "gcd equation; its only unique-multiplier result concerned field "
                            + "inverses. The proof reuses Mathlib's divisibility witness and "
                            + "positive natural multiplication cancellation.")),
                    Paragraph(Text(
                        "This closes the square/gcd exchange-parameter criterion in appendix "
                            + "E.44. It does not assert the geodesic interpretation, the "
                            + "remaining determinant equation, or the finite census."))),
                DescribeRole.Theorem))));
}
