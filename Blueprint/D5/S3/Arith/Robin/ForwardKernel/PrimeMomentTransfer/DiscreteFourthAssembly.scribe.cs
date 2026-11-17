using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class DiscreteFourthAssemblyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/DiscreteFourthAssembly.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Discrete fourth moments approach the overlap pairing uniformly on polynomial length bands.",
        H("Uniform discrete fourth moments"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("eventual-discrete-fourth"),
                DeclarationHandle.Create(Prefix + "eventual_discrete_fourth"),
                H("Uniform fourth moment asymptotic"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume the empty and singleton singular series equal one, the four-point mean-square correlation bound, and the interval correlation estimates. "
                    + "For 0<alpha<beta<1/4, M>=1 and every delta>0, the discrete fourth mixed moment divided by N*(H*log N)^2 differs from the weight integral times kappa(N,H)^2 times the three overlap pairings by at most B*delta for all sufficiently large N. "
                    + "The threshold is uniform in integer lengths N^alpha<=H<=N^beta, interval endpoints, and weights whose supremum plus total variation is at most B and which vanish outside [1,2]. "
                    + "The normalized arithmetic error, correlation modulus, and inverse logarithm all tend to zero uniformly on this band."))),
                DescribeRole.Theorem))));
}
