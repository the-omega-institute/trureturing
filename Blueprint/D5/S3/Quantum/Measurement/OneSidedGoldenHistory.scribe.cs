using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class OneSidedGoldenHistoryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete retained golden histories.", H("Complete retained golden histories"), Blocks(
            Describe.Lean(DescribeId.Create("native-predictor-minimum"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/OneSidedGoldenHistory.native_predictor_minimum"),
                H("Complete retained golden histories"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let P be any Hermitian idempotent on a finite complex matrix carrier and let E=I-P. The initial state is an arbitrary density matrix, including coherent off-diagonal blocks. Put q=Re Tr(P rho), and assume 0<q<1.")),
                    Paragraph(Text("Set x=1/phi, where phi=(1+sqrt(5))/2, and retain the relative phase zeta^(-3), where zeta=exp(3 pi i/5). The two Kraus branches are M0=sqrt(x) E and M1=x E+zeta^(-3) P. Their adjoint products sum to the identity. Branch states are M_i rho M_i*, and every outcome is retained in source order through runWord.")),
                    Paragraph(Text("The mass of every finite Boolean history is the real trace of its branch state and is strictly positive. For n consecutive one outcomes the mass equals q+(1-q)x^(2n), and the conditional P weight is q divided by this mass. The next-zero probability is the ratio of the extended-history mass to the history mass.")),
                    Paragraph(Text("After any zero, the posterior P weight is zero and the conditional next-zero probability is x. At every all-one history of length n, including n=0, it is x(1-q)x^(2n)/(q+(1-q)x^(2n)). The computation keeps both CP branches and their relative phase; it does not replace the instrument by a supplied scalar-law certificate.")),
                    Paragraph(Text("For every 0 < epsilon < x/2 there is a first nonstrict cutoff N with p(n) <= 2 epsilon exactly when N <= n. A total predictor on Fin(N+1)+Unit attains N+2 states, and every correct predictor on every finite carrier has at least this many states. This includes N=0 and threshold equality. Correctness is tested on the actual conditional trace probabilities at every positive history; it does not assume the scalar law.")),
                    Paragraph(Text("For epsilon >= x/2 a single state outputting x/2 suffices. At epsilon=0 no finite predictor is correct, because the positive age probabilities tend to zero and a finite total-update orbit must repeat. Only the state count is asserted. The natural ceiling definition of N is the ceiling of log((1-q)(x-2 epsilon)/(2 epsilon q))/(2 log phi), truncated at zero; Nat.ceil_le gives the nonstrict threshold, including integer ties. The asymptotic state and bit bounds, exact-depth augmented predictors and the degenerate q endpoints lie outside the formal statement. Supplying depth changes the state contract by supplying a clock; it does not remove the counting resource.")),
                    Paragraph(Text("The explicit Born/CP retained-readout interpretation is a model premise. The preparation coefficients are sqrt(x) I and x(E+zeta P), and the reader coefficients are the entries of B_R. Their composition equals zeta^2 times these Kraus operators in each record coordinate. The theorem also proves equality of the resulting CP branches, so this common phase does not alter the retained history law. A reconstruction for one designated preparation alone does not establish that interpretation for arbitrary inputs."))),
                DescribeRole.Theorem))));
}
