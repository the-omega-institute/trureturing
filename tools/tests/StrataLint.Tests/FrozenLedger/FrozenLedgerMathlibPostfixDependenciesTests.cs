using StrataLint.Engine;
using static StrataLint.TestSupport.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed partial class FrozenLedgerTests
{
    [Theory]
    [InlineData("ᴴ", false, "unchanged", true)]
    [InlineData("ᴴ", true, "unchanged", true)]
    [InlineData("ᴴ", false, "value", false)]
    [InlineData("ᴴ", true, "value", false)]
    [InlineData("ᴴ", false, "type", false)]
    [InlineData("ᴴ", true, "type", false)]
    [InlineData("ᴴᴴ", false, "unchanged", true)]
    [InlineData("ᴴᴴ", true, "value", false)]
    [InlineData("ᴴˣ", false, "unchanged", true)]
    [InlineData("ᴴˣ", true, "value", false)]
    [InlineData("ˣᴴ", false, "unchanged", true)]
    [InlineData("ˣᴴ", true, "value", false)]
    [InlineData("ˣ", false, "unchanged", true)]
    [InlineData("ˣ", true, "value", false)]
    public void MathlibReanchorTracksAttachedPostfixOperands(
        string postfix, bool transitive, string mutation, bool authorized)
    {
        var owner = ModuleWithReport("A", "import D5.S0.Carrier.B\ntheorem a : "
            + "D5.S0.Carrier.matrix" + postfix + " = D5.S0.Carrier.matrix" + postfix
            + " := by rfl\n", "old postfix consumer") with { Imports = ["B"] };
        var operand = ModuleWithReport("B", (transitive ? "import D5.S0.Carrier.C\n" : "")
            + "namespace D5.S0.Carrier\ndef matrix : Matrix (Fin 1) (Fin 1) Nat := "
            + "fun _ _ => " + (transitive ? "seed" : "7") + "\nend D5.S0.Carrier\n",
            "matrix", declarations: ["D5.S0.Carrier.matrix"], kind: "def")
            with { Imports = transitive ? ["C"] : [] };
        var seed = ModuleWithReport("C", "namespace D5.S0.Carrier\ndef seed : Nat := 7\nend D5.S0.Carrier\n",
            "seed", declarations: ["D5.S0.Carrier.seed"], kind: "def");
        var candidateOperand = operand with
        {
            Source = mutation == "type" ? operand.Source.Replace("Nat", "Int", StringComparison.Ordinal)
                : mutation == "value" && !transitive ? operand.Source.Replace("7", "8", StringComparison.Ordinal)
                : operand.Source,
        };
        var candidateSeed = seed with
        {
            Source = mutation == "value" && transitive ? seed.Source.Replace("7", "8", StringComparison.Ordinal)
                : seed.Source,
        };
        var result = ValidateMathlibReanchor([owner, operand, seed],
            [owner with { StatementMaterial = "new postfix consumer" }, candidateOperand, candidateSeed],
            ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.Equal(authorized, result.Authorized);
    }

    [Theory]
    [InlineData("ᴴ", false)]
    [InlineData("ᴴ", true)]
    [InlineData("ᴴᴴ", false)]
    [InlineData("ᴴᴴ", true)]
    public void MathlibReanchorRetainsExactPostfixLikeIdentifiers(string postfix, bool changeExact)
    {
        const string source = "namespace D5.S0.Carrier\ndef matrix : Nat := 7\n"
            + "def matrixᴴ : Nat := 11\nend D5.S0.Carrier\n";
        var operand = ModuleWithReport("B", source, "operand",
            declarations: ["D5.S0.Carrier.matrixᴴ"], kind: "def");
        var owner = ModuleWithReport("A", "import D5.S0.Carrier.B\n"
            + "theorem a : D5.S0.Carrier.matrix" + postfix + " = D5.S0.Carrier.matrix" + postfix
            + " := by rfl\n", "old exact identifier")
            with { Imports = ["B"] };
        var result = ValidateMathlibReanchor([owner, operand],
            [owner with { StatementMaterial = "new exact identifier" }, operand with
            {
                Source = changeExact ? source.Replace("11", "12", StringComparison.Ordinal) : source,
            }], ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.Equal(!changeExact, result.Authorized);
    }

    [Theory]
    [InlineData("missingᴴ")]
    [InlineData("missingᴴᴴ")]
    public void MathlibReanchorRefusesUnresolvedPostfixOperands(string operand)
    {
        var owner = ModuleWithReport("A", "theorem a : D5.S0.Carrier." + operand + " = 0 := by rfl\n",
            "old unresolved operand");
        var result = ValidateMathlibReanchor([owner, Module("B")],
            [owner with { StatementMaterial = "new unresolved operand" }, Module("B")],
            ["A"], ReanchorEnvironment.PinUpgrade);
        Assert.False(result.Authorized);
    }
}
