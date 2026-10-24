using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.HypergeometricShiftTuran;

internal sealed class FunctionResultDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/kalmykovkarp2017pfq");
    private const string Prefix = "D5/S3/Analytic/HypergeometricShiftTuran/FunctionResult.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A convergent-series counterexample to the function clause of Conjecture 1.",
        H("The function Turanian can be negative"), Blocks(
            Describe.Lean(DescribeId.Create("gamma-series-function"),
                DeclarationHandle.Create(Prefix + "fval"),
                H("The function in equation (10)"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Equation (10), page 5 of arXiv:1611.06724v1: “f (µ; x) = Γ(a + µ)/Γ(b + µ) pFq(a + µ; b + µ; x) = ∑ₙ₌₀∞ Γ(a + µ + n)/Γ(b + µ + n) xⁿ/n!.” Vector Gamma values denote products over entries. The Lean definition is the real tsum of Defs.coeff a b (mu+n) times x to the power n divided by n factorial. At the counterexample all three series converge, as follows from the Gamma recurrence and a geometric bound after index eight."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gamma-series-function-turanian"),
                DeclarationHandle.Create(Prefix + "turanian"),
                H("The function Turanian"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Equation (9), page 5: “∆f (α, β; x) := f (µ + α; x)f (µ + β; x) − f (µ; x)f (µ + α + β; x) = ∑ₘ₌₀∞ δm xᵐ”. The definition retains the two shifted products with exactly this subtraction order."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("conjecture-one-function-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The universal function assertion"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Theorem 3, page 5: “Theorem 3. If p ≤ q and conditions (13) are satisfied, then ∆f (α, β; x) ≥ 0 for x ≥ 0, µ, β ≥ 0 and α ∈ N, where ∆f (α, β; x) is defined in (9) with f from (10). Moreover, if α ≤ β + 1, then δm ≥ 0 for all m ∈ N0.”")),
                    Paragraph(Text("Conjecture 1, page 6: “Conjecture 1. All conclusions of Theorem 3 hold for all α, β ≥ 0 if µ ≥ 1.” The claim is precisely its function clause in the p at most q branch: all positive numerator and denominator parameter vectors satisfying Defs.cond13, all mu at least one, all nonnegative alpha, beta and x. It imposes no alpha at most beta+1 condition, since that restriction belongs to the coefficient clause. A zero-length numerator is permitted, and condition (13) is then vacuous."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("conjecture-one-function-refutation"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Refutation by an exact series estimate"),
                StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Take p=0, q=12, every denominator parameter equal to one half, mu=1, alpha=beta=1/2 and x=5000. Write A=fval at mu=3/2, fval at mu=1 as pi to the power -6 times R, and fval at mu=2 as pi to the power -6 times S. The integer and half-integer Gamma formulas give positive rational series for A, R and S.")),
                    Paragraph(Text("Use the first eight terms for each series. The tail of A is at most its term of index eight divided by 1-rho, where rho=5000/(9 times 10 to the power 12). The upper bound for A is at most 9/4. The first eight rational terms of R sum to at least 161000 and those of S to at least 34; these lower bounds already follow from their first two terms. Mathlib's pi<3.1416 and exact rational arithmetic give (9/4) squared times pi to the power 12 less than 161000 times 34. Therefore A squared is strictly smaller than pi to the power -12 times R times S. The Turanian is strictly negative.")),
                    Paragraph(Text("The dimensions, positive denominator parameters and nonnegative shifts satisfy every hypothesis of claim. Thus universal function nonnegativity is false. Theorem 3's integer-shift statement is unaffected by these two half shifts."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("kalmykov-karp-pfq-conjecture-one-function"),
                    ResolutionKind.Refuted)))));
}
