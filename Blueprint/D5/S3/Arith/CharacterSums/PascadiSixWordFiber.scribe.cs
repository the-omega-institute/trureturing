using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums;

internal sealed class PascadiSixWordFiberDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/CharacterSums/pascadi2025nonabelianamplification");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Central six-letter returns satisfy fixed-middle compatibility equations and a finite-interval count governed by their gcd period.",
        H("Pascadi Six-Word Completion Fiber"),
        Blocks(
            Paragraph(Text(
                "Pascadi's Conjecture 6.1 predicts a uniform count for alternating T,S return words in PSL₂(Z/cZ). "
                + "For c>0, units a₁,a₂ in ZMod c, and γ²=1, this module isolates the q=6 central-return equations without dividing by the possibly nonunit coefficient D. "
                + "Fix h₂,h₃,h₅,h₆ in ZMod c and write D=1−a₁a₂h₂h₃ and N=c/gcd(c,D.val). For every natural H, the number of pairs (h₁,h₄) in {0,…,H−1}² whose actual sixReturnWord equals γI is at most (⌊H/N⌋+1)². "
                + "The full uniform six-letter conjecture remains open.")),
            Describe.Lean(DescribeId.Create("pascadi-six-return-word-return-step"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiSixWordFiber.returnStep"), H("returnStep"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The elementary transfer matrix T^x S used in the six-letter return word."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("pascadi-six-return-word-definition"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiSixWordFiber.sixReturnWord"), H("sixReturnWord"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The alternating six-letter product with coefficients a₁ and a₂."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("pascadi-six-return-word-scalar"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiSixWordFiber.scalarReturn"), H("scalarReturn"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The central scalar matrix γI; composite moduli allow central scalars beyond ±I."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("pascadi-six-return-word-fiber"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiSixWordFiber.completionFiber"), H("completionFiber"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The two-coordinate completion fiber after h₂,h₃,h₅,h₆ and γ are fixed."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("pascadi-six-return-word-equations"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiSixWordFiber.completion_equations_of_sixReturnWord"), H("completion_equations_of_sixReturnWord"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "A central six-letter return forces D = γ(a₁a₂h₅h₆−1), D h₁ = γh₅−h₃, and D h₄ = γh₆−h₂. "
                    + "Only the assumed unit hypotheses on a₁ and a₂ are cancelled."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pascadi-six-return-word-period"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiSixWordFiber.completionFiber_period"), H("completionFiber_period"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Two completions in one fixed-middle fiber differ by the additive order c/gcd(c,D.val) in each free coordinate. "
                    + "Since N divides c, the same congruence holds for arbitrary natural representatives, including representatives beyond c."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pascadi-six-return-word-fixed-middle-count"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiSixWordFiber.sixReturnWord_fixed_middle_count"), H("sixReturnWord_fixed_middle_count"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Assume c>0, a₁ and a₂ are units in ZMod c, and γ²=1. Fix h₂,h₃,h₅,h₆ in ZMod c. "
                    + "For every H in ℕ, at most (⌊H/N⌋+1)² pairs (h₁,h₄) in {0,…,H−1}² satisfy sixReturnWord a₁ a₂ h₁ h₂ h₃ h₄ h₅ h₆ = γI, where N=c/gcd(c,(1−a₁a₂h₂h₃).val). "
                    + "The compatibility equations place actual solutions in the completion fiber. Its period makes the quotient map (h₁,h₄)↦(⌊h₁/N⌋,⌊h₄/N⌋) injective on those solutions; each quotient is at most ⌊H/N⌋. "
                    + "This includes H=0, composite moduli, and D=0, when N=1. It supplies a fixed-middle count, without estimating the sum over middle coordinates required by the full conjecture."))), DescribeRole.Theorem)),
        edges: []));
}
