using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Engine.Tests;

public sealed class DigestionDecompositionPolicyTests
{
    [Theory]
    [InlineData("\r")]
    [InlineData("\r\n")]
    [InlineData("\n")]
    public void ExplicitSecondaryVerdictRequiresDecompositionBeforeAbsorption(string newline)
    {
        var atom = Atom(
            $"**Theorem**. Covered claim.{newline}"
            + $"Proof: exact witness.{newline}"
            + $"**Structural verdict**: uncovered global clause.{newline}");

        Assert.True(DigestionDecompositionPolicy.IsMultiClause(atom));
        Assert.True(DigestionDecompositionPolicy.RejectsNewAbsorption(
            atom,
            DigestionMigrationState.Absorbed,
            unresolvedSubitemCount: 0,
            hasVerifiedChainAtoms: false,
            baseline: DigestionMigrationState.Partial));
        Assert.False(DigestionDecompositionPolicy.RejectsNewAbsorption(
            atom,
            DigestionMigrationState.Absorbed,
            unresolvedSubitemCount: 1,
            hasVerifiedChainAtoms: false,
            baseline: DigestionMigrationState.Partial));
        Assert.False(DigestionDecompositionPolicy.RejectsNewAbsorption(
            atom,
            DigestionMigrationState.Absorbed,
            unresolvedSubitemCount: 0,
            hasVerifiedChainAtoms: true,
            baseline: DigestionMigrationState.Partial));
    }

    [Fact]
    public void SingleClaimWithProofDoesNotRequireSyntheticDecomposition()
    {
        var atom = Atom("**Theorem**. One claim.\nProof: exact witness.\n");

        Assert.False(DigestionDecompositionPolicy.IsMultiClause(atom));
    }

    [Fact]
    public void EnumeratedClaimsRequireDecomposition()
    {
        var atom = Atom("**Verdict**:\n- first claim\n- second claim\n");

        Assert.True(DigestionDecompositionPolicy.IsMultiClause(atom));
    }

    private static DigestionAtom Atom(string text)
    {
        var bytes = Encoding.UTF8.GetBytes(text).ToImmutableArray();
        return DigestionAtom.FromFrozenCas(bytes);
    }
}
