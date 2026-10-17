// Source candidate; current Scribe compilation and emission are pending.
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Lieb;

internal sealed class SupportPerspectiveTransportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed support transport and ambient unitalization for the proposed transformer.",
        H("SupportPerspectiveTransport"), Blocks(
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
                    + "and final congruence cancellations. The full three-module proof "
                    + "and these Scribe sources await current elaboration, kernel, "
                    + "axiom and registration checks. Identity regularization and "
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
    private static Formula SignedSupport() => Seq(
        F.Id("q"), F.Id("S"), Eq, F.Id("S"), Eq, F.Id("S"), F.Id("q"), Comma, Sp,
        F.Id("S"), Eq, Call("Phi", Seq(Call("sqrt", F.Id("B")), F.Id("Z"), Call("sqrt", F.Id("B")))));
    private static Formula Localization() => Seq(
        F.Id("R"), Call("cfc", F.Id("f"), Seq(F.Id("Y"), Plus, F.Id("t"), Open, D(1), Minus, F.Id("q"), Close)),
        F.Id("R"), Eq, F.Id("R"), Call("cfc", F.Id("f"), F.Id("Y")), F.Id("R"));
    private static Formula Unitalization() => Seq(
        Call("cfc", F.Id("f"), Call("Theta", F.Id("X"))), Le,
        Call("Theta", Call("cfc", F.Id("f"), F.Id("X"))));
}
