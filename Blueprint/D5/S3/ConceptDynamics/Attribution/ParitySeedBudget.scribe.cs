using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution;

internal sealed class ParitySeedBudgetDocument : IScribeDocumentDefinition
{
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula Statement()
    {
        var n = F.Id("n");
        var budget = F.Id("N");
        var nat = F.Id("Nat");
        return Disp(All("n", nat, All("N", nat, new Formula.Logic(
            Call("Implements", n, budget), FormulaLogicOperator.Iff,
            Seq(D(2), Caret, Grp(n, Sp, Plus, Sp, D(3)), Sp, Mid, Sp, budget)))));
    }

    private static Formula FibreStatement()
    {
        var implementation = F.Id("A");
        var even = F.Id("p");
        var odd = F.Id("q");
        var n = F.Id("n");
        var count = Seq(D(4), Sp, Mid, Sp, Call("Count", implementation, even, odd));
        var profilePairs = All("p", Call("EvenProfiles", n), All("q", Call("OddProfiles", n), count));
        return Disp(All("n", F.Id("Nat"), All("A", Call("UniformImplementations", n), profilePairs)));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact uniform seed budgets for two coloured parity laws are multiples of four times a parity class.",
        H("Exact seed budgets for coloured parity profiles"),
        Blocks(Describe.Lean(
            DescribeId.Create("exact-coloured-parity-seed-budget"),
            DeclarationHandle.Create(
                "D5/S3/ConceptDynamics/Attribution/ParitySeedBudget.exact_seed_budget"),
            H("Exactly which seed counts realize the two uniform parity laws"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("The cube has n+2 coordinates for a natural number n. " +
                    "The group consists of binary acting vectors under coordinatewise addition. " +
                    "The two output sets are the even and odd profiles with one binary colour, " +
                    "respectively. The action preserves the profile and adds the acting vector " +
                    "over its zero coordinates to the colour. Implements(n,N) means there is a " +
                    "finite group set S of cardinality N and an equivariant map from S to the " +
                    "product of the two output sets, such that a common natural count k is " +
                    "the number of seeds above every output of either projection. For positive " +
                    "N these counts give the uniform laws. The empty seed set realizes N=0.")),
                Paragraph(Text("The pushforward counts are invariant. For a pair with neither " +
                    "profile all ones, the four colour counts in that cell are equal. The " +
                    "profile obtained from the all-ones vector by clearing two coordinates is in " +
                    "the same parity class and supplies a row or column entirely divisible by " +
                    "four. The common marginal then forces the remaining cells to be divisible " +
                    "by four as well. Summing the cells gives the necessary modulus.")),
                Paragraph(Text("For sufficiency, match even and odd profiles with identical " +
                    "tails. Use all four pairs of colours over each matched pair, repeated " +
                    "as many times as the budget multiplier. The copy construction gives a " +
                    "finite group set, with the prescribed cardinality and equal counts above " +
                    "every output in each parity class."))),
            DescribeRole.Theorem),
        Describe.Lean(
            DescribeId.Create("fourfold-coloured-parity-seed-fibres"),
            DeclarationHandle.Create(
                "D5/S3/ConceptDynamics/Attribution/ParitySeedBudget.profile_fibre_four_dvd"),
            H("Every ordered profile pair has a multiple of four seeds"),
            StatementSource.FromAuthor(FibreStatement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("The profiles have n+2 coordinates. A ranges over finite sets " +
                    "of seeds with the coordinate colour action and equivariant readout into " +
                    "the two coloured parity classes. Every coloured output on either side " +
                    "has the same seed count. Count(A,p,q) counts seeds whose readout profiles " +
                    "are p and q, pooling the four possible pairs of colours.")),
                Paragraph(Text("The count for a given pair is exactly the sum of its four " +
                    "coloured cells in the pushforward matrix. The common marginals transfer " +
                    "fourfold divisibility to the cells incident to the all-ones profile."))),
            DescribeRole.Theorem))));
}
