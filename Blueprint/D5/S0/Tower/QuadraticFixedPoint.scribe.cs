using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower;

internal sealed class QuadraticFixedPointDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nonzero real satisfies x^2 = x + 1 exactly when it satisfies x = 1 + 1/x.",
        H("Quadratic Fixed Point"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("quadratic-fixed-point-iff"),
                DeclarationHandle.Create(
                    "D5/S0/Tower/QuadraticFixedPoint.quadratic_fixed_point_iff"),
                H("Quadratic and reciprocal fixed-point forms"),
                StatementSource.FromAuthor(In(Seq(
                    Forall, Sp, F.Id("x"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma,
                    Esc, F.Id("x"), Neq, Sp, D(0), Sp, Rightarrow, Sp,
                    Open, F.Id("x"), Caret, Grp(D(2)), Sp, Eq, Sp,
                    F.Id("x"), Sp, Plus, Sp, D(1), Sp, Iff, Sp,
                    F.Id("x"), Sp, Eq, Sp, D(1), Sp, Plus, Sp,
                    Frac, Grp(D(1)), Grp(F.Id("x")), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a nonzero real, clearing the denominator turns the " +
                        "reciprocal equation into the quadratic equation.")),
                    Paragraph(Text(
                        "This is an honest partial closure of the leading algebraic " +
                        "clause in the source atom only; its tower, self-application, " +
                        "and Fibonacci interpretations remain unresolved."))),
                DescribeRole.Theorem)),
        []));
}
