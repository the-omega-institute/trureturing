using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FinitePhase;

internal sealed class ResidualWindowDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FinitePhase/ResidualWindow.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite stochastic matrix admits a short near-return phase, with a uniform bound for nonresonant moving averages.",
        H("Finite stochastic phase residuals and moving averages"), Blocks(
            Paragraph(Text("Let I be any finite nonempty state type, S its cardinality, and P a real matrix with nonnegative entries and each row summing to one. complexMatrix(P) is the same matrix acting on complex columns. The norm of a column is its maximum coordinate modulus. All sums over I use the whole state type. No irreducibility, aperiodicity, normality, mixing, or lower bound on a positive transition is assumed.")),
            Describe.Lean(DescribeId.Create("finite-stochastic-phase-residual"),
                DeclarationHandle.Create(Prefix + "phase_residual"),
                H("A short return phase controls the residual"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every unit complex w and nonzero complex column v, one natural return length r between 1 and S satisfies |1-w^r|^2 times the maximum norm of v at most 8S times the maximum norm of v-wP(v). Roots of unity and w=1 are included. In particular, a zero residual forces a return phase among the first S powers.")),
                    Paragraph(Text("Choose a coordinate c of v with maximal modulus M>0, and put E equal to the maximum residual modulus. At time t, consider the real part of w^t v(i) conjugate(c). A stochastic weighted average is bounded above by one of its coordinates. The residual identity therefore propagates a supporting value of at least M^2-tME to some coordinate at every natural time t.")),
                    Paragraph(Text("The selected coordinate at time t has squared distance from c, after multiplication by w^t, at most 2tME. Among times 0 through S, two selected coordinates coincide, at a<b. With r=b-a, subtracting their two deviations after rotation gives c(w^r-1). The squared triangle bound and a+b at most 2S yield M^2|1-w^r|^2 at most 8SME. Cancellation of the positive M proves the result."))),
                DescribeRole.Theorem),
            Paragraph(Text("For a real probability row alpha and a real report b with every coordinate in [0,1], write q(n)=alpha dot (P^n b). For an integer j, including negative j, phaseWindow is exactly N^{-1} times the sum, for 0<=k<N, of z^{j(m+k)} q(m+k). The displayed absolute value is the complex modulus. The starting time m is arbitrary and N is a positive natural number.")),
            Describe.Lean(DescribeId.Create("finite-stochastic-phase-window"),
                DeclarationHandle.Create(Prefix + "window_average"),
                H("A positive phase gap bounds every moving window"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Assume |z|=1, j is a nonzero integer, and gamma>0 is a lower bound for |1-z^{jr}| for every natural r between 1 and S. Then the modulus of phaseWindow is at most 16S/(N gamma^2), uniformly in m. Taking z=w and j=1 gives the bound for any unit phase w. Taking gamma to be the positive minimum of the finitely many phase gaps gives the usual minimum-gap formulation.")),
                    Paragraph(Text("Set w=z^j and u(t)=P^t b on complex columns. Stochasticity gives maximum norm at most one for every u(t), and the probability row alpha has functional norm at most one. Apply the preceding residual estimate to V=sum_{k<N} w^k u(m+k). Its residual is exactly u(m)-w^N u(m+N), so it has norm at most two. The case V=0 is handled directly; otherwise the short return length and the gamma hypothesis give gamma^2 times the norm of V at most 16S.")),
                    Paragraph(Text("The original real matrix powers and real dot product agree exactly with their complex casts. Integer powers satisfy (z^j)^t=z^{jt} for every natural t, including negative j. Thus the unnormalized original sum is w^m alpha(V); its modulus is at most the norm of V. Division by the positive N completes the estimate. A zero phase gap is excluded by the explicit positive hypothesis, and no inverse operator is needed."))),
                DescribeRole.Theorem),
            Paragraph(Text("These estimates concern finite stochastic readouts and phase averages. They establish neither the complete native finite-memory separation theorem, the algebraic phase gap for the original system, nor its original state realization.")))));
}
