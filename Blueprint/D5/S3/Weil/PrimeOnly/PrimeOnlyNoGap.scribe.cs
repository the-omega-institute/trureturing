using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.PrimeOnly;

internal sealed class PrimeOnlyNoGapDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Weil/PrimeOnly/PrimeOnlyNoGap.numberField_prime_only_no_gap";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The prime-only jump Laplacian has nonnegative nonzero-mode energies whose infimum "
            + "vanishes throughout the absolutely convergent half-plane.",
        H("Prime-Only No-Gap Theorem"),
        Blocks(Describe.Lean(
            DescribeId.Create("number-field-prime-only-no-gap"),
            DeclarationHandle.Create(Declaration),
            H("Prime-only spectral coefficients have no positive uniform gap"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The jump indices are positive powers of genuine prime ideals in a number "
                        + "field. Dedekind-zeta convergence for sigma greater than one makes "
                        + "their weights summable.")),
                Paragraph(Text(
                    "Compact recurrence in every finite product of regulator circles gives a "
                        + "nonzero integer mode simultaneously close to the identity for any "
                        + "finite collection of prime-power shifts. No irrationality premise "
                        + "on the shifts is needed.")),
                Paragraph(Text(
                    "A finite-tail split then makes the Fourier jump energy arbitrarily small. "
                        + "Nonnegativity supplies the reverse bound, so the infimum over the "
                        + "subtype of nonzero integer modes is exactly zero."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula sigma = F.Id("sigma");
        Formula n = F.Id("n");
        Formula coefficient = new Formula.Subscript(F.Id("C"), n);
        Formula nonzeroIntegers = F.Seq(
            OpenBrace, n, InMacro, Sp, F.Id("Z"), Sp, Mid, Sp,
            n, Sp, Neq, Sp, D(0), CloseBrace);
        Formula infimum = Call("inf", nonzeroIntegers, coefficient);
        return Disp(F.Seq(
            sigma, Sp, Gt, Sp, D(1), Sp, Rightarrow, Sp,
            infimum, Sp, Eq, Sp, D(0), Dot));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
