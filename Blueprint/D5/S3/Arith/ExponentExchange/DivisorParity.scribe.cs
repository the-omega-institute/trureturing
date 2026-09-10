using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.ExponentExchange;

internal sealed class DivisorParityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime-factor parity determines the commutation sign of divisor reflection.",
        H("Divisor Parity and Reflection"),
        Blocks(Describe.Lean(
            DescribeId.Create("factor-parity-reflection"),
            DeclarationHandle.Create("D5/S3/Arith/ExponentExchange/DivisorParity.factor_parity_reflection"),
            H("Divisor-operator commutation sign"),
            StatementSource.FromAuthor(Disp(Seq(
                Gamma, Sp, F.Id("R"), Eq, Open, Minus, D(1), Close,
                Caret, Grp(Operatorname, Grp(F.Id("cardFactors")), Open, F.Id("N"), Close),
                F.Id("R"), Gamma))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "Let N be a nonzero natural number. On the complex coefficient space of its "
                + "divisors, Gamma multiplies the d coefficient by the sign of its prime-factor "
                + "count, with multiplicity. R precomposes coefficients with d mapped to N/d; "
                + "this involution sends the d basis vector to the N/d basis vector. "
                + "The repository operator interface applies Mathlib's cardFactors_mul and "
                + "normalizes the resulting powers of minus one."))),
            DescribeRole.Theorem))));
}
