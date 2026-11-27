using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.UnorderedTrees;

internal sealed class ForkDecorationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normalized fork decorations correspond bijectively to the actual qualifying rooted-tree classes.",
        H("Unordered fork decorations"),
        Blocks(Describe.Lean(
            DescribeId.Create("unordered-decoration-classification"),
            DeclarationHandle.Create("D5/S3/Combinatorics/UnorderedTrees/ForkDecoration.classification"),
            H("A bijection at each total size"),
            StatementSource.FromAuthor(Disp(Seq(
                Forall, Sp, F.Id("n"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                new Formula.Subscript(F.Id("W"), F.Id("n")), Sp, Equiv, Sp,
                new Formula.Subscript(F.Id("T"), F.Id("n"))))),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Tₙ is the type of classes of actual parent maps on Fin n for which "
                    + "vertex height equals internal-vertex count. Wₙ consists of fork "
                    + "parameters b and c, one nonnegative leaf multiplicity at each of "
                    + "the b+c+1 spine nonterminals, and two nonnegative tip offsets. "
                    + "The tip multiplicities are one plus those offsets. At c=0 the offsets "
                    + "are sorted. The weight is b+c+5 plus the sum of all offsets and "
                    + "spine multiplicities, and equals n.")),
                Paragraph(Text(
                    "Inflation followed by labelling the carrier gives the forward map. "
                    + "The inverse prunes the original leaves and reads the multiplicities "
                    + "on the canonical fork. Fork depth and maximum depth fix b and c. "
                    + "A fork automorphism fixes the nonterminals in depth order and can "
                    + "exchange tips only when c=0. Sorting removes that ambiguity, "
                    + "including the case of equal fibre sizes."))),
            DescribeRole.Definition))));
}
