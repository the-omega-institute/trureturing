using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms;

internal sealed class PrimaryPseudoperfectPortsDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix = "D5/S3/PrimeForms/PrimaryPseudoperfectPorts.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Primary pseudoperfect numbers admit an exact reciprocal-sum characterization.",
        H("Primary Pseudoperfect Reciprocal Identity"),
        Blocks(
            Paragraph(Text(
                "Write d(n) for the sum of n divided by p over the distinct prime divisors p "
                    + "of n, and R(n) for the corresponding sum of rational reciprocals 1/p.")),
            Describe.Lean(
                DescribeId.Create("squarefree-derivative-rational-cast"),
                DeclarationHandle.Create(DeclarationPrefix + "squarefreeDeriv_cast"),
                H("The quotient sum casts to the reciprocal-prime sum"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("d", N), Sp, Eq, Sp, N, Sp, Call("R", N), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every prime in primeFactors n divides n and is nonzero. Mathlib's "
                        + "Nat.cast_div therefore converts each natural quotient n / p to the "
                        + "rational quotient, and distributivity factors out n."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reciprocal-sum-equals-one-iff"),
                DeclarationHandle.Create(DeclarationPrefix + "reciprocal_sum_eq_one_iff"),
                H("The reciprocal and integral identities are equivalent"),
                StatementSource.FromAuthor(Disp(Seq(
                    N, Sp, Neq, Sp, D(0), Sp, Rightarrow, Sp,
                    new Formula.Fraction(D(1), N), Sp, Plus, Sp, Call("R", N), Sp,
                    Eq, Sp, D(1), Sp, Leftrightarrow, Sp,
                    N, Sp, Eq, Sp, D(1), Sp, Plus, Sp, Call("d", N), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Multiplication by the nonzero rational n and the cast identity turn one "
                        + "equation into the other. The explicit nonzero premise excludes the "
                        + "totalized division value at n = 0."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("primary-pseudoperfect-reciprocal-characterization"),
                DeclarationHandle.Create(DeclarationPrefix + "isPPN_iff_reciprocal_sum"),
                H("Primary pseudoperfectness is the reciprocal identity"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("IsPPN", N), Sp, Leftrightarrow, Sp,
                    Call("Squarefree", N), Sp, Land, Sp, D(1), Sp, Lt, Sp, N, Sp, Land, Sp,
                    new Formula.Fraction(D(1), N), Sp, Plus, Sp, Call("R", N), Sp,
                    Eq, Sp, D(1), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The strict lower bound n > 1 supplies n != 0 in both directions, so the "
                        + "reciprocal theorem applies without a hidden degenerate case."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula N => F.Id("n");
}
