using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.ModularForms;

internal sealed class IntegralDiscriminantDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Fourier/mathlib2026modularforms");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An integral divisor-sum series for the actual analytic modular discriminant, with finite coefficient computation.",
        H("Integral Analytic Discriminant"),
        Blocks(
            Paragraph(Text(
                "For r a natural number let U_r have coefficient sigma_r(n), the sum of the r-th powers of the positive divisors of n. The divisor set at zero is empty. Put U=U_3 and V=U_5. The normalized weight-four and weight-six Eisenstein series have q-expansions 1+240U and 1-504V.")),
            Describe.Lean(
                DescribeId.Create("integral-eisenstein-four"),
                DeclarationHandle.Create("D5/S3/Arith/ModularForms/IntegralDiscriminant.integralEisensteinFour_map"),
                H("Weight-four integral series"),
                StatementSource.FromAuthor(EisensteinFormula(D(4))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Mapping integralEisensteinFour coefficientwise through the integer embedding into the complex numbers gives qExpansion 1 E4, for Mathlib's actual analytic normalized Eisenstein form. EisensteinSeries.E_qExpansion_coeff supplies its divisor-sum formula; bernoulli(4)=-1/30 supplies the factor 240. This identity is used in the discriminant comparison."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("integral-eisenstein-six"),
                DeclarationHandle.Create("D5/S3/Arith/ModularForms/IntegralDiscriminant.integralEisensteinSix_map"),
                H("Weight-six integral series"),
                StatementSource.FromAuthor(EisensteinFormula(D(6))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Mapping integralEisensteinSix coefficientwise gives qExpansion 1 E6 for the actual analytic form. The same normalized Eisenstein formula, with bernoulli(6)=1/42, supplies the factor -504. Both series have constant coefficient one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("integral-discriminant-analytic-map"),
                DeclarationHandle.Create("D5/S3/Arith/ModularForms/IntegralDiscriminant.integralDiscriminant_map"),
                H("The integer series is the actual discriminant"),
                StatementSource.FromAuthor(Disp(Seq(Call("map", F.Id("D")), Sp, Eq, Sp,
                    Call("qExpansion", D(1), Delta)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every integer d, 5d^3+7d^5 is zero modulo 3 and modulo 4. These coprime divisibilities imply divisibility by 12. Summing over divisors proves that C_n=(5 sigma_3(n)+7 sigma_5(n))/12 is an exact integer quotient, including n=0.")),
                    Paragraph(Text(
                    "Set D=C+100U^2-147V^2+8000U^3. The exact quotient identity gives 1728D=(1+240U)^3-(1-504V)^2. Mathlib's discriminant_eq_E4_cube_sub_E6_sq identifies the corresponding actual analytic functions. Compatibility of qExpansion with scalar multiplication, subtraction and powers then proves map(D)=qExpansion 1 Delta. Thus every analytic discriminant coefficient is an integer; division by 1728 alone is not the integrality argument.")),
                    Paragraph(Text(
                    "The accompanying Mathlib source note records the pinned Eisenstein and analytic discriminant suppliers and links the existing Ribet-Stein Hecke context. The integer denominator-clearing realization and the finite coefficient bridge are repository proofs of classical modular-form infrastructure; no unique result, new verified Maeda case or mathematical originality is claimed. The full Miller basis and actual Hecke matrix construction remain unresolved."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("discriminant-integer-coefficient-algorithm"),
                DeclarationHandle.Create("D5/S3/Arith/ModularForms/IntegralDiscriminant.discriminantCoefficient_correct"),
                H("Executable integer coefficients"),
                StatementSource.FromAuthor(Disp(All("n", F.Id("N"),
                    Seq(Call("a", Delta, F.Id("n")), Sp, Eq, Sp,
                        Call("cast", Call("discriminantCoefficient", F.Id("n"))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "discriminantCoefficient(n) computes the exact quotient C_n and finite convolution coefficients for 100U^2-147V^2+8000U^3. Each convolution sums i from 0 through n. Nested convolution computes the cube. The function uses integer arithmetic and finite divisor sets, with no analytic coefficient evaluation or selected inverse. For every n its integer output, embedded in the complex numbers, equals coefficient n of the actual analytic discriminant.")),
                    Paragraph(Text(
                    "At every natural precision N, PowerSeries.trunc_apply and Fin.sum_univ_eq_sum_range turn this coefficient theorem into equality between the analytic truncation and the polynomial of integer outputs at indices n<N. This application is checked transiently rather than retained as a separate theorem. Precision pm+1 includes coefficient pm. IntegralMillerBasis constructs the normalized integral basis and full coefficient lattice for m>=1 and s in 0,4,6,8,10,14 at weight 12m+s. The actual Hecke matrix and finite-array precision correctness remain to be proved."))),
                DescribeRole.Theorem))));


    private static Formula EisensteinFormula(Formula weight) =>
        Disp(Seq(Call("map", new Formula.Subscript(F.Id("E"), weight)), Sp,
            Eq, Sp, Call("qExpansion", D(1), new Formula.Subscript(F.Id("E"), weight))));

    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Sp, Colon, Sp, type, Comma, Sp, body);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
}
