using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Thermal;

internal sealed class PositiveOneModeWilliamsonDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every positive one-mode quadratic energy has a positive symplectic normal form.",
        H("Positive One-Mode Williamson Form"),
        Blocks(Describe.Lean(
            DescribeId.Create("positive-one-mode-williamson"),
            DeclarationHandle.Create(
                "D5/S3/Quantum/Thermal/PositiveOneModeWilliamson.positive_one_mode_williamson"),
            H("A positive quadratic form becomes an isotropic oscillator"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For a real symmetric positive-definite two-by-two matrix S, there is a "
                        + "positive frequency omega and a symplectic matrix M with "
                        + "M-transpose S M equal to omega times the identity.")),
                Paragraph(Text(
                    "The symplectic identity uses the physical q,p Poisson matrix "
                        + "with upper-right entry +1 and lower-left entry -1. "
                        + "This statement has one mode; the general finite-mode normal form "
                        + "requires a separate construction."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula a = F.Id("a"), b = F.Id("b"), c = F.Id("c");
        Formula s = Call("matrix2", a, b, b, c);
        Formula m = F.Id("M"), omega = F.Id("omega");
        Formula j = Call("matrix2", D(0), D(1),
            Seq(Minus, D(1)), D(0));
        return Disp(Seq(Forall, Sp, a, Comma, Sp, b, Comma, Sp, c, Comma, Sp,
            Call("PosDef", s), Sp, Rightarrow, Sp, Exists, Sp, omega, Comma, Sp, m,
            Comma, Sp, new Formula.Relation(D(0), FormulaRelationOperator.LessThan, omega),
            Sp, Land, Sp,
            Equal(Multiply(Multiply(Call("transpose", m), j), m), j), Sp, Land, Sp,
            Equal(Multiply(Multiply(Call("transpose", m), s), m),
                Multiply(omega, F.Id("I")))));
    }
}
