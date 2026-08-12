using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.PureState;

internal sealed class PureStateHandshakeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A pure state sandwiches any matrix to a scalar multiple of itself.",
        H("The Pure-State Handshake"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("pure-state-handshake-sandwich-collapse"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/PureState/PureStateHandshake.pure_state_handshake"),
                H("The pure-state sandwich collapses to a scalar"),
                StatementSource.FromAuthor(Disp(Seq(
                    Rho, Sp, F.Id("X"), Sp, Rho, Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("inner")), Open, F.Id("v"), Comma, Sp,
                    F.Id("X"), Sp, F.Id("v"), Close, Sp, Cdot, Sp, Rho, Comma, RowBreak,
                    Rho, Sp, Rho, Sp, Eq, Sp, Rho, Comma, Sp,
                    Operatorname, Grp(F.Id("inner")), Open, F.Id("v"), Comma, Sp,
                    F.Id("X"), Sp, F.Id("v"), Close, Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("Tr")), Open, F.Id("X"), Sp, Rho, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a normalized amplitude vector v (inner product of v with itself equal to 1), "
                        + "the rank-one density matrix rho = |v><v| — the outer product with entries "
                        + "rho i j = v i times conjugate of v j — is idempotent (rho times rho = rho), so "
                        + "a pure state is its own square root.")),
                    Paragraph(Text(
                        "The handshake is the middle identity: for ANY matrix X, sandwiching X between "
                        + "two copies of rho collapses to a scalar multiple, rho X rho = <v, X v> times "
                        + "rho, and that scalar equals the density-matrix expectation Tr(X rho). "
                        + "Specializing X to an inverse state gives the mechanism behind the pure-state "
                        + "divergence handshake. The load-bearing new content is this sandwich-collapse "
                        + "identity — there is no library lemma for rho X rho with a general middle matrix "
                        + "— while the idempotency and the expectation-equals-trace fact are its "
                        + "supporting glue. Only the normalization <v,v> = 1 is used, and only for "
                        + "idempotency; the handshake and the trace identity hold for every v and every "
                        + "X, with no positivity or invertibility hypothesis.")),
                    Paragraph(Text(
                        "Only the algebraic handshake mechanism is recorded here. The downstream "
                        + "conclusion — that the Belavkin-Staszewski and max divergences of a pure state "
                        + "against sigma both equal the logarithm of <v, sigma-inverse v> — is not "
                        + "covered by this statement."))),
                DescribeRole.Theorem))));
}
