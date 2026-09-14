using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography;

internal sealed class HolomorphicSublevelInvarianceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual derivative, center and forcing budgets imply a complex-ball self-map uniformly over a family of certified node choices.",
        H("Complex residual-band Newton invariance"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("holomorphicsublevelinvariance-complex-sublevel-newton-ball-invariant"),
                DeclarationHandle.Create("D5/S3/Quantum/Tomography/HolomorphicSublevelInvariance.complex_sublevel_newton_ball_invariant"),
                H("complex sublevel newton ball invariant"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each node use fixed C and actual derivative J. If norm(I-CJ) is at most q on the complex ball, center displacement is at most b, norm(C) is at most kappa, and b+kappa gamma+q r is at most r, then z-C(f(z)-e) stays in the same ball for all norm(e) at most gamma. No external PASS, root existence, inverse Jacobian or global cover is assumed. Exclusion and split nodes retain their set-theoretic semantics."))),
                DescribeRole.Theorem))));
}
