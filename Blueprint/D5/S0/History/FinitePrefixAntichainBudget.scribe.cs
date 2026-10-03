using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.History;

internal sealed class FinitePrefixAntichainBudgetDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite prefix antichains inherit local child budgets at the root.",
        H("Finite Prefix Antichain Budget"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-prefix-antichain-budget"),
            DeclarationHandle.Create("D5/S0/History/FinitePrefixAntichainBudget.result"),
            H("Local budgets bound every finite prefix antichain"),
            StatementSource.FromAuthor(Disp(Seq(
                Sum, Underscore, Grp(F.Id("h"), InMacro, FormulaDsl.Sp, F.Id("K")), Sp,
                F.Id("m"), Open, F.Id("h"), Close, Leq, Sp,
                F.Id("m"), Open, F.Id("nil"), Close))),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let E be any type with decidable equality and V an additive "
                    + "commutative monoid with a preorder preserved by addition. Suppose that, "
                    + "for every word h and every finite set C of letters, the sum of m(h ++ [a]) "
                    + "over a in C is at most m(h). For every finite set K of words such that "
                    + "a prefix relation between two members forces equality, the sum of m over K "
                    + "is then at most m of the empty word. No finite alphabet, subtraction, "
                    + "scalar multiplication, lattice or topology is assumed.")),
                Paragraph(Text("The proof inducts on a finite upper bound for word lengths. "
                    + "A member equal to the empty word forces a singleton. Otherwise the words "
                    + "partition by their occurring first letters. Removing that letter gives "
                    + "shorter prefix antichains; the shifted budget inherits the local hypothesis. "
                    + "Finite sum regrouping and monotonicity combine their inductive bounds, "
                    + "and the root local bound finishes. The empty antichain is included because "
                    + "the empty child selection implies nonnegativity. This is a mathematical "
                    + "supplier, not a claim that an actual controller satisfies its hypothesis."))),
            DescribeRole.Theorem))));
}
