// Signed support transport and ambient unitalization for finite positive maps.
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Lieb;

internal sealed class SupportPerspectiveTransportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed support transport and ambient unitalization for the supported transformer.",
        H("SupportPerspectiveTransport"), Blocks(
            Describe.Lean(DescribeId.Create("spectral-square-root-normalization"),
                DeclarationHandle.Create("D5/S3/Quantum/Lieb/SupportPerspectiveTransport.spectral_sqrt_normalization"),
                H("Normalize the actual spectral square root"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "For every finite decidable carrier n and PSD Q in M_n(C), let "
                    + "R=sqrt(Q), W=spectralInverseSqrt(Q), and P=spectralSupport(Q). "
                    + "Then R*=R, W*=W, P*=P, P P=P, P R=R, R P=R, P Q=Q, "
                    + "and W Q W=P. These are consumed specializations of the existing "
                    + "singleton square-root Kraus support and normalization results. "
                    + "The empty carrier and Q=0 are included."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("signed-positive-map-support"),
                DeclarationHandle.Create("D5/S3/Quantum/Lieb/SupportPerspectiveTransport.positive_map_sandwich_support"),
                H("Positive maps preserve support of signed sandwiches"),
                StatementSource.FromAuthor(SignedSupport()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For an arbitrary finite positive complex-linear map Phi, PSD B, "
                    + "and Hermitian Z, put S=Phi(sqrt(B) Z sqrt(B)) and "
                    + "q=spectralSupport(Phi(B)). Then q S = S = S q. Hermitian "
                    + "norm bounds give -norm(Z) Phi(B) <= S <= norm(Z) Phi(B); "
                    + "positivity and zero Gram matrices force support. This argument "
                    + "does not require Z, f(Z), or f(0) to be nonnegative. The "
                    + "support facts are supplied by the existing spectralSupport "
                    + "and spectralInverseSqrt definitions and singleton-sqrt Kraus "
                    + "specializations of SpectralTransposeRecovery."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("supported-cfc-localization"),
                DeclarationHandle.Create("D5/S3/Quantum/Lieb/SupportPerspectiveTransport.cfc_supported_localization"),
                H("Localize CFC through a supported sandwich"),
                StatementSource.FromAuthor(Localization()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For Hermitian projection q, Hermitian Y with qY=Y, and R "
                    + "satisfying qR=R=Rq, every real t and every real function f "
                    + "satisfy R cfc(f,Y+t(I-q)) R = R cfc(f,Y) R. The proof "
                    + "uses the rectangular intertwining theorem with intertwiner q. "
                    + "No independent block functional-calculus premise is assumed."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ambient-unitalized-jensen"),
                DeclarationHandle.Create("D5/S3/Quantum/Lieb/SupportPerspectiveTransport.ambient_unitalized_jensen"),
                H("Apply Jensen to an explicit ambient unitalization"),
                StatementSource.FromAuthor(Unitalization()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For PSD B and any positive complex-linear Phi, define "
                    + "N(Z)=Phi(B)^{+1/2} Phi(sqrt(B) Z sqrt(B)) Phi(B)^{+1/2}. "
                    + "The plus exponent denotes the existing spectral inverse square "
                    + "root, zero on the kernel, not an algebraic inverse. The "
                    + "singleton Kraus normalization gives N(I)=q, with "
                    + "q=spectralSupport(Phi(B)). Choose an input coordinate i and "
                    + "set Theta(Z)=N(Z)+Z_ii (I-q). Coordinate evaluation is a "
                    + "positive unital complex-linear state, so Theta is positive "
                    + "unital, even when Phi(B)=0. The new positive-map Jensen "
                    + "bridge gives cfc(f,Theta(X)) <= Theta(cfc(f,X)) for PSD X, "
                    + "the full all-Hilbert operator-convex supplier and continuity. "
                    + "This is a concrete construction, not a unitality assumption "
                    + "on Phi.")), Paragraph(Text(
                    "SupportPerspectiveTransformer consumes these interfaces and supplies "
                    + "the exact kernel-inclusion reconstruction, mixed spectral products "
                    + "and final congruence cancellations. The Jensen and transport "
                    + "modules and the transformer have passed explicit targeted "
                    + "Lean builds and a joint scoped report using only standard "
                    + "Lean axioms. Information-audit binding is assessed separately. "
                    + "Identity regularization and "
                    + "trace data processing remain outside this source endpoint."))), DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complex => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Mat(string n) => Call("Matrix", F.Id(n), F.Id(n), Complex);
    private static Formula Binder(string name, Formula type) => Seq(F.Id(name), Colon, Sp, type, Comma, Esc);
    private static Formula Instance(string name, string n) => Seq(OpenBracket, Call(name, F.Id(n)), CloseBracket, Comma, Sp);
    private static Formula Carrier(string n, string u) => Seq(Binder(n, Call("Type", F.Id(u))),
        Instance("Fintype", n), Instance("DecidableEq", n));
    private static Formula Carriers(bool mixed) => Seq(Forall, Sp, Binder("u", Call("Level")),
        mixed ? Binder("v", Call("Level")) : Seq(), Carrier("n", "u"), Carrier("m", mixed ? "v" : "u"));
    private static Formula PositiveMap => Call("PositiveLinearMap", Complex, Mat("n"), Mat("m"));
    private static Formula SignedSupport() => Disp(Seq(Carriers(true),
        Binder("Phi", PositiveMap), Binder("B", Mat("n")), Binder("Z", Mat("n")),
        Binder("q", Mat("m")), Binder("S", Mat("m")),
        Call("PSD", F.Id("B")), Comma, Sp, Call("Hermitian", F.Id("Z")), Comma, Sp,
        F.Id("q"), Eq, Call("spectralSupport", Call("Phi", F.Id("B"))), Comma, Sp,
        F.Id("S"), Eq, Call("Phi", Seq(Call("sqrt", F.Id("B")), F.Id("Z"), Call("sqrt", F.Id("B")))),
        Sp, Implies, Sp,
        F.Id("q"), F.Id("S"), Eq, F.Id("S"), Eq, F.Id("S"), F.Id("q")));
    private static Formula Localization() => Disp(Seq(Forall, Sp, Binder("u", Call("Level")), Carrier("n", "u"),
        Binder("q", Mat("n")), Binder("Y", Mat("n")), Binder("R", Mat("n")),
        Binder("t", Real), Binder("f", Seq(Real, Sp, To, Sp, Real)),
        Call("Hermitian", F.Id("q")), Comma, Sp, F.Id("q"), F.Id("q"), Eq, F.Id("q"), Comma, Sp,
        Call("Hermitian", F.Id("Y")), Comma, Sp, F.Id("q"), F.Id("Y"), Eq, F.Id("Y"), Comma, Sp,
        F.Id("q"), F.Id("R"), Eq, F.Id("R"), Comma, Sp, F.Id("R"), F.Id("q"), Eq, F.Id("R"),
        Sp, Implies, Sp,
        F.Id("R"), Call("cfc", F.Id("f"), Seq(F.Id("Y"), Plus, F.Id("t"), Open, D(1), Minus, F.Id("q"), Close)),
        F.Id("R"), Eq, F.Id("R"), Call("cfc", F.Id("f"), F.Id("Y")), F.Id("R")));
    private static Formula Theta(Formula x) => Call("ambientUnitalization", F.Id("Phi"), F.Id("B"), F.Id("i"), x);
    private static Formula Unitalization() => Disp(Seq(Carriers(false),
        Binder("f", Seq(Real, Sp, To, Sp, Real)), Binder("Phi", PositiveMap),
        Binder("B", Mat("n")), Binder("i", F.Id("n")), Binder("X", Mat("n")),
        Call("OperatorConvexOnAll", F.Id("u"), Call("Ici", D(0)), F.Id("f")), Comma, Sp,
        Call("ContinuousOn", F.Id("f"), Call("Ici", D(0))), Comma, Sp,
        Call("PSD", F.Id("B")), Comma, Sp, Call("PSD", F.Id("X")), Sp, Implies, Sp,
        Call("cfc", F.Id("f"), Theta(F.Id("X"))), Le,
        Theta(Call("cfc", F.Id("f"), F.Id("X")))));
}
