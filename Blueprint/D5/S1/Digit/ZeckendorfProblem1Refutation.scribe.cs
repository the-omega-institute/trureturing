using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class ZeckendorfProblem1RefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Digit/ZeckendorfProblem1Refutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Digit/moradi2026fibonaccilinear");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal refutation of the complete Fibonacci-DFAO Problem 1 statement.",
        H("Moradi--Rampersad--Shallit Problem 1: exact partial MSD model"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("zeckendorfproblem1refutation-problem1"),
                DeclarationHandle.Create(Prefix + "Problem1"),
                H("Problem 1 as full eventual uniform linear bounds"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The exact Lean definition is `Problem1 : Prop := ∃ a b : ℝ, "
                    + "0 < a ∧ 0 < b ∧ ∃ c0 : ℕ, ∀ c : ℕ, c0 ≤ c → "
                    + "a * c ≤ minimumStates c ∧ (minimumStates c : ℝ) ≤ b * c`. "
                    + "Here minimumStates c is the attained minimum over reachable finite "
                    + "partial MSD Fibonacci machines for shift c. A machine is correct for "
                    + "every valid padded no-adjacent-ones word, starts at a counted zero-loop "
                    + "state, omits a sink, and is undefined on invalid words. The empty word and every all-zero word output t(c), where t(n) is the parity of the occupied canonical Fibonacci digits."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("zeckendorfproblem1refutation-problem1-refuted"),
                DeclarationHandle.Create(Prefix + "problem1_refuted"),
                H("Literal negation of Problem 1"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The complete theorem statement is `theorem problem1_refuted : ¬ Problem1`, namely ¬ (∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∃ c0 : ℕ, ∀ c : ℕ, c0 ≤ c → a * c ≤ minimumStates c ∧ (minimumStates c : ℝ) ≤ b * c). "
                    + "It uses the full source machine class and all-word Option semantics. "
                    + "Finite residual realization supplies an ordinary reachable partial machine "
                    + "with the counted initial zero-loop; contextual replacement and normalized "
                    + "state covers give an unbounded Fibonacci family with a sublinear state-count "
                    + "upper bound. For H ≥ 14, put φ = (1 + √5)/2, δ = 1 − φ^(−14), and C = 128(2φ + 1). The proof bounds minimumStates(F_H) / F_H by C δ^floor(H/14), with 0 ≤ δ < 1. The positive shifts F_H are unbounded. The ratio tends to zero along this family, which refutes the "
                    + "original positive uniform lower bound for all sufficiently large c."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "moradi-rampersad-shallit-2026-fibonacci-shift-linear-refutation"),
                    ResolutionKind.Refuted))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Digit/ZeckendorfRawWindow")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Digit/ZeckendorfCarryBarrier")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Digit/ZeckendorfContextualReplacement")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Digit/ZeckendorfResidualCover")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Digit/ZeckendorfResidualMachine")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Digit/ZeckendorfResidualNormalForm")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Digit/ZeckendorfAvoidanceCount"))
        ]));
}
