using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Conventions;

internal sealed class ComplementEncodingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Subtraction complement is involutive and determines its total.",
        H("Complement Encoding"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("complement-encoding"),
                DeclarationHandle.Create(
                    "D5/S0/Conventions/ComplementEncoding.complement_encoding"),
                H("Complement encoding"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("G"), Comma, Sp,
                    F.Id("u"), Comma, Sp, F.Id("e"), InMacro, Sp, F.Id("G"), Comma, Esc,
                    F.Id("c"), Underscore, F.Id("u"), Open, D(0), Close, Eq, F.Id("u"),
                    Sp, Land, Sp,
                    F.Id("c"), Underscore, F.Id("u"), Open, F.Id("u"), Close, Eq, D(0),
                    Sp, Land, Sp,
                    F.Id("c"), Underscore, F.Id("u"), Open,
                    F.Id("c"), Underscore, F.Id("u"), Open, F.Id("e"), Close, Close,
                    Eq, F.Id("e"), Sp, Land, Sp,
                    Open, Forall, Sp, F.Id("v"), Comma, Sp,
                    F.Id("c"), Underscore, F.Id("v"), Eq,
                    F.Id("c"), Underscore, F.Id("u"), Sp, Rightarrow, Sp,
                    F.Id("v"), Eq, F.Id("u"), Close, Comma, Esc,
                    F.Id("c"), Underscore, F.Id("u"), Open, F.Id("x"), Close,
                    Colon, Eq, F.Id("u"), Minus, F.Id("x"), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For an additive commutative group, complementing e relative to u is "
                        + "the subtraction u - e. The theorem records the endpoint values, "
                        + "the involution law, and recovery of u from the value at zero.")),
                    Paragraph(Text(
                        "Pinned Mathlib was searched before proving. The exact algebraic hits "
                        + "were sub_zero, sub_self, and sub_sub_self; the proof is a direct "
                        + "application of these library lemmas. Repository searches found no "
                        + "existing declaration for this total-recovery complement statement.")),
                    Paragraph(Text(
                        "This deposit closes only the complement-encoding clause at "
                        + "qdo-v1 theorem/38.1 for atom "
                        + "qdo-residual-ef4826943d8848ca382a11dd9ef8e07ab2930ca795c5645aeb15b92f5a4c0662. "
                        + "No claim is made about other residual clauses."))),
                DescribeRole.Theorem))));
}
