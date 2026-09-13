using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FluidDynamics.Fourier;

internal sealed class ToralIsogenyShearNSDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FluidDynamics/Fourier/ToralIsogenyShearNS.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original integer torus bridge transports an explicit NS shear only with its metric; keeping the Euclidean metric produces an exact nonzero residual.",
        H("The metric-sensitive Navier-Stokes bridge"),
        Blocks(
            Paragraph(Text("Let k be a natural number. Write s_lambda(t,x,y)=(1,k) exp(-nu lambda t) "
                + "cos(-2kx+2y). R_H(v) denotes the full ordinary-derivative expression "
                + "partial_t v+(v dot grad)v-nu(h00 partial_xx+2h01 partial_xy+h11 partial_yy)v. "
                + "Pressure and external forcing are identically zero. H is a constant symmetric inverse "
                + "metric when it is positive definite; the residual formula itself allows arbitrary real coefficients.")),
            Describe.Lean(DescribeId.Create("actual-shear-divergence"),
                DeclarationHandle.Create(Prefix + "shear_divergence"),
                H("The actual smooth periodic field is incompressible"),
                StatementSource.FromAuthor(Disp(Seq(
                    Quantify("nu,lambda,t,x,y"),
                    Call("div", Call("s", F.Id("lambda"))), Sp, Eq, Sp, D(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The source differentiates the literal exponential-cosine functions. "
                    + "The covector (-2k,2) has zero pairing with the velocity direction (1,k), so divergence "
                    + "vanishes. The same source proves joint smoothness and actual 2*pi spatial periodicity "
                    + "in both coordinates. All times and real rates are included in the identities."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("full-shear-ns-residual"),
                DeclarationHandle.Create(Prefix + "shear_residual"),
                H("The full convection-diffusion residual is computed"),
                StatementSource.FromAuthor(Disp(Seq(
                    Quantify("nu,lambda,h00,h01,h11,t,x,y"),
                    Forall, Sp, F.Id("i"), Colon, Sp, Call("Fin", D(2)), Comma, Sp,
                    Residual(F.Id("h00"), F.Id("h01"), F.Id("h11"), Call("s", F.Id("lambda"))),
                    Sp, Eq, Sp,
                    Call("mul", F.Id("nu"), Coefficient(), Call("s_component", F.Id("lambda"), F.Id("i")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed coefficient is 4h00*k^2-8h01*k+4h11-lambda. "
                    + "The proof derives time, first and second coordinate derivatives using HasDerivAt. "
                    + "It retains both nonlinear advective terms and proves their cancellation on this invariant "
                    + "shear family. It does not infer nonlinear perturbation stability from that cancellation."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("transported-metric-solution"),
                DeclarationHandle.Create(Prefix + "pulled_metric_solution"),
                H("The genuine vector pullback solves the metric-transported equation"),
                StatementSource.FromAuthor(Disp(Seq(
                    Quantify("nu,t,x,y"),
                    Forall, Sp, F.Id("i"), Colon, Sp, Call("Fin", D(2)), Comma, Sp,
                    Call("div", F.Id("v")), Sp, Eq, Sp, D(0), Sp, Land, Sp,
                    Residual(D(1), F.Id("k"), Call("add", Call("square", F.Id("k")), Call("div", D(1), D(4))), F.Id("v")),
                    Sp, Eq, Sp, D(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("P_k is read from the original ToralReturnModuleSpectrum bridge, not reidentified "
                    + "by its name. Its real tangent inverse is Q=[[1,0],[k,1/2]]. The source derives "
                    + "G=P^T P, H=Q Q^T=[[1,k],[k,k^2+1/4]], both inverse identities, and positivity "
                    + "through (r+ks)^2+s^2/4. The field v=Q u(t,P(x,y)), with "
                    + "u=(exp(-nu*t)cos(y),0), is proved equal to s_1 before the residual theorem is applied. "
                    + "Q is not a global inverse of the degree-two torus covering."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("euclidean-metric-defect"),
                DeclarationHandle.Create(Prefix + "pulled_euclidean_defect"),
                H("An unchanged Euclidean metric leaves a quantified defect"),
                StatementSource.FromAuthor(Disp(Seq(
                    Quantify("nu,t,x,y"),
                    Forall, Sp, F.Id("i"), Colon, Sp, Call("Fin", D(2)), Comma, Sp,
                    Residual(D(1), D(0), D(1), F.Id("v")), Sp, Eq, Sp,
                    Call("mul", F.Id("nu"), Call("add", Call("mul", D(4), Call("square", F.Id("k"))), D(3)),
                        Call("v_component", F.Id("i")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The identity is R_I(v)=nu*(4k^2+3)*v. At t=x=y=0, component zero "
                    + "equals nu*(4k^2+3), strictly positive whenever nu>0; "
                    + "pulled_euclidean_defect_positive proves that literal witness. This excludes the "
                    + "assertion that the arithmetic intertwiner alone preserves unchanged Euclidean NS."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("corrected-euclidean-evolution"),
                DeclarationHandle.Create(Prefix + "euclidean_shear_solution"),
                H("The same initial field has a different exact Euclidean decay rate"),
                StatementSource.FromAuthor(Disp(Seq(
                    Quantify("nu,t,x,y"),
                    Forall, Sp, F.Id("i"), Colon, Sp, Call("Fin", D(2)), Comma, Sp,
                    Call("div", CorrectedShear()), Sp, Eq, Sp, D(0), Sp, Land, Sp,
                    Residual(D(1), D(0), D(1), CorrectedShear()), Sp, Eq, Sp, D(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The corrected rate is lambda=4(k^2+1), the squared Euclidean frequency "
                    + "of (-2k,2). The source separately proves equality of the two literal initial fields. "
                    + "All calculations concern smooth planar, unforced, zero-pressure periodic shears. "
                    + "They do not establish general three-dimensional regularity, a cat map particle realization, "
                    + "or arbitrary-data equivalence. The 2*pi convention is kept distinct from the period-one "
                    + "arithmetic torus. Classical context is Fannjiang-Wolowski (math/0209231) for noisy toral "
                    + "transport and Arnaudon-Cruzeiro-Fang (1509.03491) for metric-dependent NS formulations."))),
                DescribeRole.Theorem))));

    private static Formula Quantify(string realVariables) => Seq(
        Forall, Sp, F.Id("k"), Colon, Sp, Call("Nat"), Comma, Sp,
        Forall, Sp, F.Id(realVariables), Colon, Sp, Call("Real"), Comma, Sp);
    private static Formula Coefficient() => Call("sub",
        Call("add", Call("sub", Call("mul", D(4), F.Id("h00"), Call("square", F.Id("k"))),
            Call("mul", D(8), F.Id("h01"), F.Id("k"))), Call("mul", D(4), F.Id("h11"))),
        F.Id("lambda"));
    private static Formula CorrectedShear() => Call("s",
        Call("mul", D(4), Call("add", Call("square", F.Id("k")), D(1))));
    private static Formula Residual(Formula h00, Formula h01, Formula h11, Formula field) =>
        Call("R", F.Id("nu"), h00, h01, h11, field, F.Id("t"), F.Id("x"), F.Id("y"), F.Id("i"));
    private static Formula Call(string name, params Formula[] arguments)
    {
        var pieces = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0) pieces.AddRange([Comma, Sp]);
            pieces.Add(arguments[i]);
        }
        pieces.Add(Close);
        return Seq([.. pieces]);
    }
}
