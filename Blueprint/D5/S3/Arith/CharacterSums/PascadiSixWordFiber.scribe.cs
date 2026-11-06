using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums;

internal sealed class PascadiSixWordFiberDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/CharacterSums/pascadi2025nonabelianamplification");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fixed-middle six-letter PSL₂ return fiber is forced by entrywise compatibility equations and has a gcd-periodic completion coordinate.",
        H("Pascadi Six-Word Completion Fiber"),
        Blocks(
            Paragraph(Text(
                "Pascadi's Conjecture 6.1 predicts a uniform count for alternating T,S return words in PSL₂(Z/cZ). "
                + "This module isolates the q=6 central-return equations without dividing by the possibly nonunit coefficient D.")),
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
                    + "This is the gcd-periodic stratum needed for a bounded representative count."))), DescribeRole.Theorem)),
        edges: []));
}
