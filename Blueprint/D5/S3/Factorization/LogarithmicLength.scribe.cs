using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization;

internal sealed class LogarithmicLengthDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Apostol =
        LibraryNoteRef.Create("D5/L/apostol1976introduction");

    private static LeanDeclarationRef LeanDefinition(string value) =>
        LeanDeclarationRef.Create(
            value,
            expectedKind: LeanDeclarationKind.Definition,
            requireNoSorry: true);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A natural number's logarithm is the exponent-weighted sum of its prime-factor logarithms.",
        H("Logarithmic Length from Prime Factorization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("factorization-logarithmic-length"),
                DeclarationHandle.Create("D5/S3/Factorization/LogarithmicLength.factorizationLogLength"),
                H("Prime exponents define logarithmic length"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                                    "The logarithmic length of a natural number is the finite sum over "
                                    + "its prime-factorization support, weighting the logarithm of each "
                                    + "prime by that prime's exponent."))),
                DescribeRole.Definition
            ),
            Describe.Lean(
                DescribeId.Create("factorization-logarithmic-length-equals-log"),
                DeclarationHandle.Create("D5/S3/Factorization/LogarithmicLength.factorization_log_length_eq_log"),
                H("Prime-factor length equals the natural logarithm"),
                StatementSource.FromAuthor(Disp(Seq(
                                    Forall, Sp, F.Id("n"), InMacro, Sp,
                                    Mathbb, Grp(F.Id("N")), Comma, Esc,
                                    Operatorname, Grp(F.Id("factorizationLogLength")),
                                    Open, F.Id("n"), Close, Eq,
                                    Operatorname, Grp(F.Id("log")), Open, F.Id("n"), Close))),
                AssessedProvenance.FromLiterature(Apostol),
                Blocks(
                                    Paragraph(Text(
                                        "For every natural number, the additive length read from its "
                                        + "prime exponents equals its real logarithm. For positive inputs "
                                        + "this is the logarithm of the unique prime-power product; the "
                                        + "zero input is included using the pinned library's conventions "
                                        + "for the logarithm and factorization at zero. The identity is "
                                        + "the exact bridge from multiplicative factorization coordinates "
                                        + "to an additive real-valued readout asserted by the source atom.")),
                                    Paragraph(Text(
                                        "The library was searched before proving. Pinned mathlib already "
                                        + "contains the complete identity as "
                                        + "Real.log_nat_eq_sum_factorization, supported internally by "
                                        + "Finsupp.log_prod and Nat.prod_factorization_pow_eq_self. The "
                                        + "Lean theorem is therefore a declared thin honest wrapper that "
                                        + "only reverses the upstream equality to place the defined length "
                                        + "on the left; no independent proof or stronger uniqueness claim "
                                        + "is presented. The source atom contains no numerical certificate."))),
                DescribeRole.Theorem
            ))));
}
