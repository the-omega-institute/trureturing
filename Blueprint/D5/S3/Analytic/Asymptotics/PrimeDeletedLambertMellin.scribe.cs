using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Asymptotics;

internal sealed class PrimeDeletedLambertMellinDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A prime-deleted Lambert heat kernel has the expected Mellin product.",
        H("Prime-Deleted Lambert--Mellin Bridge"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-deleted-lambert-mellin-bridge"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Asymptotics/PrimeDeletedLambertMellin."
                        + "prime_deleted_lambert_mellin"),
                H("The deleted Lambert kernel has a zeta-product Mellin transform"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a prime p and an integer r greater than one, the public coefficient "
                            + "primeDeletedDivisorSum is the finite divisor-antidiagonal sum that "
                            + "retains d to the negative r power exactly when p does not divide d. "
                            + "The public heat kernel is the resulting exponential series over "
                            + "positive indices; its zero coefficient vanishes.")),
                    Paragraph(Text(
                        "The displayed binders reproduce the Lean signature: p and r are natural "
                            + "numbers, p is prime, r is greater than one, w is complex, and the "
                            + "real part of w is greater than one. These assumptions imply the "
                            + "second absolute-convergence inequality for w plus r.")),
                    Paragraph(Text(
                        "The proof identifies the explicit deletion predicate with the trivial "
                            + "Dirichlet character modulo p, rewrites the divisor coefficient as a "
                            + "Dirichlet convolution, and proves heat-series summability from a "
                            + "linear coefficient bound. Mathlib's generic Mellin theorem then "
                            + "supplies the Gamma integral and interchange, while the trivial "
                            + "character formula supplies the deleted Euler factor."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula prime = F.Id("p");
        Formula exponent = F.Id("r");
        Formula w = F.Id("w");
        Formula shift = Seq(w, Sp, Plus, Sp, exponent);
        Formula kernel = Call("primeDeletedLambertKernel", prime, exponent);
        Formula deletedFactor = Seq(
            Open,
            D(1), Sp, Minus, Sp,
            new Formula.Power(prime, Grp(Seq(Minus, Grp(shift)))),
            Close);
        Formula rightHandSide = Seq(
            Gamma, Open, w, Close, Sp,
            Zeta, Open, w, Close, Sp,
            Zeta, Open, shift, Close, Sp,
            deletedFactor);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp,
                Typed(prime, natural), Comma, Sp,
                Typed(exponent, natural), Comma, Sp,
                Typed(w, complex), Semi),
            Seq(
                Grp(), Call("Prime", prime), Sp, Land, Sp,
                D(1), Sp, Lt, Sp, exponent, Sp, Land, Sp,
                D(1), Sp, Lt, Sp, Re, Open, w, Close, Sp, Rightarrow),
            Seq(
                Grp(), Call("mellin", kernel, w), Sp, Eq, Sp,
                rightHandSide, Dot),
        ]));
    }

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }
}
