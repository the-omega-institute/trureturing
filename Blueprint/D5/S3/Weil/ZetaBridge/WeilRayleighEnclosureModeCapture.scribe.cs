using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class WeilRayleighEnclosureModeCaptureDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaBridge/WeilRayleighEnclosureModeCapture.";

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
        Formula lower = F.Id("ell"), upper = F.Id("M"), threshold = F.Id("T");
        Formula k = F.Id("k"), u = F.Id("u"), A = F.Id("A");
        Formula alpha = Call("inner", k, u);
        Formula residual = Seq(u, Minus, alpha, Sp, k);
        Formula conclusion = Seq(
            D(0), Lt, Sp, threshold, Minus, upper, Land, Sp,
            Grp(threshold, Minus, upper), Sp, Call("normSq", residual),
            Leq, Sp, upper, Minus, lower);

        return DocumentDefinition.Create(ScribeNode.Create(
            "Two-sided Rayleigh enclosure and codimension-one coercivity capture the "
                + "ground eigendirection without requiring a small operator residual.",
            H("Weil Rayleigh Enclosure Mode Capture"),
            Blocks(
                Paragraph(Text(
                    "D is a real linear operator domain, iota:D->H is its embedding into "
                    + "a real Hilbert space and A:D->H is a symmetric operator action on "
                    + "that domain. The theorem is therefore compatible with an unbounded "
                    + "Friedrichs realization rather than replacing it by a bounded matrix. "
                    + "The arithmetic application must separately establish the real-invariant "
                    + "domain bridge for the canonical Weil form.")),
                Describe.Lean(
                    DescribeId.Create("rayleigh-enclosure-mode-capture"),
                    DeclarationHandle.Create(Owner + "rayleigh_enclosure_mode_capture"),
                    H("A certified Rayleigh interval captures the ground line"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Call("SymmetricOnDomain", A), Land, Sp,
                        Call("Normalized", k), Land, Sp, Call("Normalized", u), Land, Sp,
                        Call("GroundEigenpair", A, u), Land, Sp,
                        lower, Leq, Sp, Call("GroundEigenvalue", A, u), Leq, Sp,
                        Call("Rayleigh", A, k), Leq, Sp, upper, Land, Sp,
                        Call("ComplementEnergyAtLeast", A, k, threshold), Land, Sp,
                        upper, Lt, Sp, threshold, Rightarrow, Sp, conclusion))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Write alpha=<k,u> and v=u-alpha*k. Symmetry and the eigenvalue "
                        + "equation give the exact identity q(v)=lambda*||v||^2 "
                        + "+alpha^2*(q(k)-lambda). Cauchy-Schwarz gives alpha^2<=1. "
                        + "The coercive lower bound on k-perp then yields "
                        + "(T-M)||v||^2<=M-ell. This replaces the usual residual/gap "
                        + "quantity by three values directly exposed by a Schur or LDL "
                        + "certificate: a ground lower bound ell, a candidate upper bound M "
                        + "and a complementary threshold T. No claim about an unbounded-scale "
                        + "Xi limit is made by this theorem itself."))),
                    DescribeRole.Theorem))));
    }
}
