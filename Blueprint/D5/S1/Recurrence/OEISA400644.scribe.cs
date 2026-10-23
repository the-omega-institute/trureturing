using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class OEISA400644Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/OEISA400644.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact rounded three-term norm sequence has the Tribonacci square-root ratio limit.",
        H("OEIS A400644: exact rounded recurrence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("oeis-a400644-source-round"),
                DeclarationHandle.Create(Prefix + "sourceRound"),
                H("Source integer rounding operation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every nonnegative integer radicand s, Nat.sqrt s is the lower integer candidate and the threshold s > r²+r selects r+1. This is the exact integer operation in the published Python source."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("oeis-a400644-source-round-spec"),
                DeclarationHandle.Create(Prefix + "sourceRound_spec"),
                H("Two integer candidates bracket every source radicand"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The integer square root brackets s between r² and (r+1)², and sourceRound s is exactly r or r+1."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("oeis-a400644-source-round-error"),
                DeclarationHandle.Create(Prefix + "sourceRound_real_error"),
                H("Strict half-unit source rounding error"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Integer radicands cannot have a half-integer square root. Consequently the source operation differs from the real square root by strictly less than one half for every nonnegative integer radicand."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("oeis-a400644-sequence"),
                DeclarationHandle.Create(Prefix + "a"),
                H("The zero-based source sequence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The sequence starts 0, 0, 1 and applies the published rounded square-root recurrence at every later index. Source index n≥1 is represented by a(n−1)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("oeis-a400644-recurrence"),
                DeclarationHandle.Create(Prefix + "a_recurrence"),
                H("Exact recurrence at every index"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural n, a(n+3) is exactly sourceRound of the sum of the three preceding squares."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("oeis-a400644-monotone"),
                DeclarationHandle.Create(Prefix + "a_mono"),
                H("The source sequence is monotone"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Each term is at least the preceding term. This follows from the lower square-root candidate in the exact source rounding operation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("oeis-a400644-positive"),
                DeclarationHandle.Create(Prefix + "a_pos"),
                H("Eventual denominator positivity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every term from the third zero-based term onward is at least one, so the eventual consecutive ratios have positive denominators."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("oeis-a400644-unique"),
                DeclarationHandle.Create(Prefix + "a_unique"),
                H("Uniqueness of the recursively constructed sequence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Any natural-valued sequence with the same three initial values and the same exact recurrence agrees pointwise with a."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("oeis-a400644-rho"),
                DeclarationHandle.Create(Prefix + "rho_is_largest_positive_root"),
                H("The Tribonacci square-root is the largest positive sextic root"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "rho is the positive square root of the Tribonacci constant. It satisfies rho⁶−rho⁴−rho²−1=0, and every positive real root of this polynomial is at most rho."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("oeis-a400644-target-claim"),
                DeclarationHandle.Create(Prefix + "targetClaim"),
                H("Full infinite ratio limit target"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The claim includes the infinite limit of a(n+3)/a(n+2), root identification, the exact positive-index recurrence, uniqueness on positive indices, positive denominators, and the same ratio limit for every sequence satisfying the published initial data and recurrence."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("oeis-a400644-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The exact infinite consecutive-ratio limit"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For the unique nonnegative integer sequence on positive indices with a(1)=a(2)=0 and a(3)=1, the recurrence a(n+1)=Round(sqrt(a(n)^2+a(n-1)^2+a(n-2)^2)) holds for every n at least 3. Its consecutive ratio tends to rho, the largest positive real root of x^6-x^4-x^2-1=0. Every denominator from the third positive index is positive.")),
                    Paragraph(Text("The integer rounding threshold has strict error less than one half, so no tie convention changes any step. Monotonicity and the three-input square-root estimate give a(n+5) at least a(n+2)+1 in zero-based coordinates. Induction on blocks implies that the actual rounded terms tend to infinity.")),
                    Paragraph(Text("Write lambda for the Tribonacci constant and b(n)=a(n+2)^2. The signed error e(n)=b(n+3)-b(n+2)-b(n+1)-b(n) satisfies |e(n)| at most 2 a(n+4). The positive projection T(n)=b(n+2)+(lambda-1)b(n+1)+b(n)/lambda obeys T(n+1)=lambda T(n)+e(n), with T(n) at least b(n+2). Hence e(n)/T(n) tends to zero and T(n+1)/T(n) tends to lambda.")),
                    Paragraph(Text("The bounded coordinates v(n)=b(n+2)/T(n) lie in [0,1]. Their recurrence has limiting coefficients alpha=(lambda-1)/lambda and beta=lambda^(-3), both nonnegative with alpha+beta less than one. Put U=1/(1+alpha+beta). The deviations d(n)=v(n)-U satisfy d(n+2)=w(n)-alpha d(n+1)-beta d(n), where w(n) tends to zero because the coefficients converge and v is bounded.")),
                    Paragraph(Text("For M(k)=max(|d(2k)|,|d(2k+1)|), the two-step estimate gives M(k+1) at most (alpha+beta)M(k)+(1+alpha)(|w(2k)|+|w(2k+1)|). The strict affine-contraction theorem yields M(k) tending to zero. Both parities are contained in these maxima, so v(n) tends to U over all natural indices. Since U is positive, b(n+3)/b(n+2) tends to lambda. Continuity of the real square root yields the original consecutive-ratio limit.")),
                    Paragraph(Text("Finally rho^2=lambda converts the Tribonacci cubic into the sextic equation. Every positive sextic root x has x^2 greater than one and satisfies the Tribonacci cubic; cubic-root uniqueness forces x=rho. The shift sourceA(n)=a(n-1) gives the exact published indexing, and strong induction gives uniqueness on positive indices.")),
                    Paragraph(Text("The theorem-specific typed registrations retain their compiled evidence. Source selections remain unresolved, with null certificates and source.selection_missing, under https://github.com/the-omega-institute/trureturing/issues/16003. No declared_validated status is asserted. The published statement and bounded literature scope are given in the A400644 problem dossier and its Library note."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a400644-rounded-three-term-norm"),
                    ResolutionKind.Proved)))));
}
