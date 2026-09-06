using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class WeilNeumannGammaBoundaryDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaBridge/WeilNeumannGammaBoundary.";
    private static Formula Call(string name, params Formula[] args)
    {
        var items = new System.Collections.Generic.List<Formula>
            { Operatorname, Grp(F.Id(name)), Open };
        for (int i = 0; i < args.Length; i++)
        {
            if (i > 0) { items.Add(Comma); items.Add(Sp); }
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq(items.ToArray());
    }

    public DocumentDefinition Create()
    {
        Formula a=F.Id("a"), b=F.Id("b"), x=F.Id("x"), y=F.Id("y");
        Formula S=F.Id("S"), v=F.Id("v"), R=F.Id("R");
        return DocumentDefinition.Create(ScribeNode.Create(
            "Neumann Green-kernel completion supplies positive canonical Gamma boundary corrections.",
            H("Neumann completion of the actual Gamma resolvent"),
            Blocks(
                Paragraph(Text(
                    "The free and Neumann Green kernels are independently specified. "
                    + "Their difference is proved to have a positive rank-two factorization. "
                    + "The canonical Gamma rates are exactly b_r=2r+1/2. "
                    + "L2 integration, the infinite-mixture domain identity and the "
                    + "energy-weighted arithmetic Schur application are paper bridges, "
                    + "not conclusions of this Lean owner. Lean and Scribe compilation "
                    + "have not been run in this increment.")),
                Describe.Lean(DescribeId.Create("free-laplace-kernel"),
                    DeclarationHandle.Create(Owner+"freeLaplaceKernel"),
                    H("Compressed whole-line kernel"),
                    StatementSource.FromAuthor(Disp(Call("Kfree", b,x,y))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("Kfree(b,x,y)=exp(-b*abs(x-y)). For b>0 this is 2b times the whole-line resolvent kernel."))),
                    DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("neumann-laplace-kernel"),
                    DeclarationHandle.Create(Owner+"neumannLaplaceKernel"),
                    H("Independent Neumann Green formula"),
                    StatementSource.FromAuthor(Disp(Call("KN", a,b,x,y))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Set E=exp(ba), u=exp(b*min(x,y)), w=exp(b*max(x,y)). "
                        + "KN=(E*u+E^(-1)*u^(-1))*(E*w^(-1)+E^(-1)*w)/(E^2-E^(-2)). "
                        + "On [-a,a], a,b>0, this is 2b times the Neumann Green kernel. "
                        + "The operator interpretation is established separately on paper."))),
                    DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("even-boundary-response"),
                    DeclarationHandle.Create(Owner+"evenBoundaryResponse"),
                    H("Even response"),
                    StatementSource.FromAuthor(Disp(Call("Hplus", b,x))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("Hplus(b,x)=exp(bx)+exp(bx)^(-1), twice cosh(bx)."))),
                    DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("odd-boundary-response"),
                    DeclarationHandle.Create(Owner+"oddBoundaryResponse"),
                    H("Odd response"),
                    StatementSource.FromAuthor(Disp(Call("Hminus", b,x))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("Hminus(b,x)=exp(bx)-exp(bx)^(-1), twice sinh(bx)."))),
                    DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("neumann-laplace-boundary-completion"),
                    DeclarationHandle.Create(Owner+"neumann_laplace_boundary_completion"),
                    H("Exact positive boundary completion"),
                    StatementSource.FromAuthor(Disp(Call("BoundaryCompletion", a,b,x,y))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "For a,b>0 and arbitrary real x,y, KN-Kfree equals "
                        + "Hplus(x)*Hplus(y)/(2*(exp(ba)^2-1)) "
                        + "+Hminus(x)*Hminus(y)/(2*(exp(ba)^2+1)). "
                        + "All denominators are proved nonzero. Ordering x and y identifies "
                        + "the free exponential; exact field algebra proves the difference."))),
                    DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("neumann-laplace-boundary-energy"),
                    DeclarationHandle.Create(Owner+"neumann_laplace_boundary_energy"),
                    H("Finite quadratic identity"),
                    StatementSource.FromAuthor(Disp(Call("BoundaryEnergyIdentity", a,b,S,x,v))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "For any finite sample set S and real coefficients v, the double "
                        + "quadratic sum of KN-Kfree equals the sum of the squares of "
                        + "sum v_i*Hplus(x_i) and sum v_i*Hminus(x_i), divided by their "
                        + "respective positive denominators. No coefficient parity or "
                        + "boundary cancellation is assumed. The empty sample set is allowed."))),
                    DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("neumann-laplace-boundary-energy-nonneg"),
                    DeclarationHandle.Create(Owner+"neumann_laplace_boundary_energy_nonneg"),
                    H("Finite Gram positivity"),
                    StatementSource.FromAuthor(Disp(Call("BoundaryEnergyNonnegative", a,b,S,x,v))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The preceding independently derived kernel identity proves "
                        + "nonnegativity of every finite real quadratic sample. "
                        + "This does not assume positivity of the Weil form."))),
                    DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("canonical-gamma-resolvent-boundary-nonneg"),
                    DeclarationHandle.Create(Owner+"canonical_gamma_resolvent_boundary_nonneg"),
                    H("Canonical Gamma mixture"),
                    StatementSource.FromAuthor(Disp(Call("CanonicalGammaBoundaryNonnegative", a,R,S,x,v))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "For a>0 and every natural R, summing the actual kernel corrections "
                        + "over rates b_r=2r+1/2, r<R, preserves finite quadratic positivity. "
                        + "R=0 is included. The proof has no spectral-gap, residual, "
                        + "zeta-zero or target-positivity premise. Infinite positive summation "
                        + "and the Fourier/Neumann spectral identification are separate "
                        + "analytic obligations described in the existing theory volume."))),
                    DescribeRole.Theorem))));
    }
}
