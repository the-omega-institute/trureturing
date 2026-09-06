using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaLinear;

internal sealed class ProjectiveRayleighCaptureDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaLinear/ProjectiveRayleighCapture.";

    private static Formula Call(string name, params Formula[] args)
    {
        var result = new System.Collections.Generic.List<Formula>
            { Operatorname, Grp(F.Id(name)), Open };
        for (int i = 0; i < args.Length; i++)
        {
            if (i > 0) { result.Add(Comma); result.Add(Sp); }
            result.Add(args[i]);
        }
        result.Add(Close);
        return Seq(result.ToArray());
    }

    public DocumentDefinition Create()
    {
        Formula ell = F.Id("ell"), U = F.Id("U"), T = F.Id("T");
        Formula lambda = F.Id("lambda"), mu = F.Id("mu"), alpha = F.Id("alpha");
        Formula k = F.Id("k"), u = F.Id("u"), A = F.Id("A"), iota = F.Id("iota");
        Formula E = Call("normSq", Call("alignedError", iota, k, u));
        Formula enclosure = Seq(
            Call("SymmetricOnDomain", iota, A), Land,
            Call("NormalizedCandidate", iota, k), Land,
            Call("NonzeroEigenvector", iota, A, u, lambda), Land,
            ell, Leq, lambda, Lt, T, Land, mu, Leq, U, Lt, T, Land,
            Call("ComplementCoercive", iota, A, k, T));
        return DocumentDefinition.Create(ScribeNode.Create(
            "An actual symmetric operator-domain equation yields a sharp complex projective "
                + "eigenline enclosure and consumes the recorded prime-three scalar endpoints.",
            H("Complex Projective Rayleigh Capture"), Blocks(
                Paragraph(Text(
                    "D is a complex linear operator domain; iota:D->H and A:D->H are linear. "
                    + "Only the candidate k has unit embedded norm. The embedded eigenvector u "
                    + "is nonzero and satisfies Au=lambda*iota(u), with real lambda below T. "
                    + "Write mu=Re<iota(k),Ak> and alpha=<iota(k),iota(u)>. The complement "
                    + "coercivity assumption concerns every domain vector orthogonal to iota(k). "
                    + "No bounded action on all of H or small operator residual is assumed.")),
                Describe.Lean(
                    DescribeId.Create("complex-projective-rayleigh-enclosure"),
                    DeclarationHandle.Create(Owner + "projective_rayleigh_enclosure"),
                    H("The sharp aligned eigenline estimate"),
                    StatementSource.FromAuthor(Disp(Seq(
                        enclosure, Rightarrow,
                        Call("Nonzero", alpha), Land,
                        E, Leq, Call("ratio", Seq(mu, Minus, lambda), Seq(T, Minus, lambda)), Land,
                        E, Leq, Call("ratio", Seq(U, Minus, ell), Seq(T, Minus, ell)), Land,
                        E, Lt, D(1)))),
                    AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                        "Shift the action to B=A-lambda*iota. It is symmetric on the same domain "
                        + "and annihilates u. Complement coercivity first proves alpha is nonzero. "
                        + "The vector f=alpha^{-1}u-k lies in the orthogonal complement, and "
                        + "symmetry gives <iota(f),Bf>=<iota(k),Bk>. Hence "
                        + "(T-lambda)||iota(f)||^2<=mu-lambda. Since mu<T, the error is below one. "
                        + "Using (lambda-ell)(1-||iota(f)||^2)>=0 yields the endpoint ratio "
                        + "with denominator T-ell. The proof does not assume its conclusion."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("prime-three-projective-rational-comparison"),
                    DeclarationHandle.Create(Owner + "prime_three_projective_ratio"),
                    H("Exact endpoint arithmetic"),
                    StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The endpoints are ell=103/2000000000, U=560909/10000000000000 and "
                        + "T=1/200000, taken from the actual prime3_refined_certificate.json in "
                        + "PR #5602 at b02e0787252c1239cf18c6f39652048a45793f39. Their ratio is "
                        + "15303/16495000 and is strictly below (61/2000)^2. This arithmetic "
                        + "does not validate the upstream interval program or its operator bridge."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("prime-three-projective-mode-consequence"),
                    DeclarationHandle.Create(Owner + "prime_three_projective_mode_capture"),
                    H("The recorded endpoints imply a projective distance below 0.0305"),
                    StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The general domain theorem and exact rational comparison supply the last "
                        + "variational implication for the prime-three certificate. Its symmetry, "
                        + "eigenpair, candidate upper energy and codimension-one coercivity remain "
                        + "explicit hypotheses. Their realization by the arithmetic Weil operator "
                        + "is a separate proof obligation. No asymptotic Xi convergence or new "
                        + "prime-gap record follows from this fixed-window conclusion alone."))),
                    DescribeRole.Theorem),
                Paragraph(Text(
                    "This formalizes a concrete paper-level step of the ground-mode research. "
                    + "The method is classical variational analysis; no first-discovery claim is "
                    + "made. Source review and independent finite algebra checks are distinct "
                    + "from Lean elaboration, axiom inspection and Scribe emission."))
            )));
    }
}
