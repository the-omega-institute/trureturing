using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.SequentialDecisionRisk;

internal sealed class FiniteMarkovEverHitDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Estimation/SequentialDecisionRisk/FiniteMarkovEverHit.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Least harmonic hitting functions for finite stochastic kernels.",
        H("Finite-step probabilities and the harmonic hitting function"),
        Blocks(
            Paragraph(Text("Let S be any finite state space and W a real nonnegative stochastic matrix. Fix distinct states d0 and d1 whose rows are the corresponding point masses. The function hitWithin(W,d1,0,x) is the indicator of x=d1, and hitWithin(W,d1,n+1,x) is the W-row average of hitWithin(W,d1,n). Define everHit(W,d1,x) as the supremum of these values over all natural n. Time zero is included. Future(S,n) is the complete finite space of n subsequent states; futureMass is the product of the corresponding transition weights, and visits records whether the initial state or any of those n states equals d1.")),
            Describe.Lean(
                DescribeId.Create("finitemarkoveverhit-ever-hit-harmonic"),
                DeclarationHandle.Create(Prefix + "ever_hit_harmonic"),
                H("The least hitting solution without auxiliary termination"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite S and every such W,d0,d1, everHit lies in [0,1], equals zero at d0 and one at d1, and is harmonic for W at every state. For each starting state, the finite-step values converge to everHit. Each finite-step value is exactly the sum over Future(S,n) of futureMass times the indicator of visits, so it is the probability of hitting d1 by that horizon. Finally, if g is any nonnegative real function with g(d1)>=1 and Wg<=g at every state, then everHit<=g pointwise. Thus this is the least nonnegative harmonic solution with target value one. The finite-path hit events increase with the horizon, so their supremum is the eventual hitting probability under a process realizing these finite laws. Closed non-target recurrent classes remain in the state space; neither almost-sure hitting of a decision label, a mean hitting time, irreducibility nor a spectral gap is required. The only absorbing rows assumed are the two specified decision labels. The conclusion supplies a harmonic test function; it does not identify a raw observer, its initial law, a stationary epoch law or its paid operational cost."))),
                DescribeRole.Theorem))));
}
