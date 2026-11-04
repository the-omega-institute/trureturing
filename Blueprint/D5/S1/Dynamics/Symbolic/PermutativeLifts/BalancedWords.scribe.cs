using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic.PermutativeLifts;

internal sealed class BalancedWordsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedWords.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equal-height factorial words with common outer thirds.",
        H("Equal-height factorial words with common outer thirds"),
        Blocks(
            Describe.Lean(DescribeId.Create("construction"), DeclarationHandle.Create(Owner + "balancedWord"),
                H("Balanced substitution"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At level zero the word of type a is the single letter a. Put N=(n+1)!. The next false word is 2N copies of the false child followed by N copies of the true child; the next true word is N false children followed by 2N true children. Both lengths are h(n+1)=3N h(n), with h(0)=1. The number of false letters is strictly greater in the false word, proving type injectivity despite the equal lengths."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("common-thirds"), DeclarationHandle.Create(Owner + "balancedWord_common_prefix"),
                H("Shared columns and recurrence"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Both next words share their first N false children and their last N true children. Each shared segment has exactly one third of the next height. Every child type occurs in every next word. At levels n at least one, every ordered pair of level-n words occurs in every level-(n+2) word; the pair true-false uses an internal parent seam. These are combinatorial inputs for an equal-height tiling construction, not a claim that its subshift or its Toeplitz points have already been constructed."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("disagreement"), DeclarationHandle.Create(Owner + "disagreement_fraction"),
                H("Exact disagreement fraction"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Mismatch count compares aligned letters of the two equal-length lists. Splitting the two next words into three regions of N children leaves agreement on the first and third regions and N copies of the previous comparison in the middle. Thus d(n+1)=N d(n), d(0)=1, and 3^n d(n)=h(n). In particular the exact rational proportion of mismatching columns is (1/3)^n. Converting these column counts into periodic-skeleton density requires the separate tiling and phase construction."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("finite-holonomy"), DeclarationHandle.Create(Owner + "balancedWord_holonomy_eq_one"),
                H("Finite group holonomy"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any finite group G and letter map from Bool to G, both level-(n+1) word holonomies are the identity whenever the cardinality of G is at most n+1. Holonomy places the last letter on the left. The two child holonomies are separately raised to factorial multiples, so each factor is the identity; unrelated group elements are never commuted. This is a finite algebraic statement and does not by itself establish a dynamical conjugacy or resolve Kang--Jaeger Question 1.10."))), DescribeRole.Theorem))));
}
