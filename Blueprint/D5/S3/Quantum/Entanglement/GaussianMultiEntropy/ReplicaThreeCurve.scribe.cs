using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.GaussianMultiEntropy;

internal sealed class ReplicaThreeCurveDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeCurve.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The labelled B=C=b curve has A=N-2b and positive scalar domain 0<b<N/2. Its derivative has the sign of b-N/3, its continuous minimum is uniquely N/3, and its two scalar endpoint limits are zero. Physical sizes additionally must be positive integers.",
        H("The labelled equal-party curve and its boundaries"),
        Blocks(
            Paragraph(Text("Scientific source: Haobo Ma then Wenlin Zhang, An exact balancing law for order-three Gaussian multi-entropy, 4 November 2026, CC BY 4.0; Camargo and Nishida for the fully symmetric pure Gaussian family and equal-party observation. Size dependence here is not a dynamical evaporation theorem. The source's real scalar interpolation does not assert fractional physical modes.")),
            Node("curve", "The scalar B=C curve", "curve",
                "F(k,N,b)=V(k,N-2b,b,b). For k>0 and N>0 its positive scalar domain is 0<b<N/2. For actual fixed integer total N>=3 and squeezing a>1, use k=kappa(N,a).", DescribeRole.Definition),
            Node("coefficient", "The exact derivative coefficient", "curveDerivative",
                "Put A=N-2b, M=1+k(2Nb-3b^2), L=1+2kb(N-2b), R=1+kb(N-b). The exact coefficient is k^2 b(3b-N)[N+k(2A^2 b+3Ab^2+2b^3)]/(6LRM). In the positive scalar domain every factor except 3b-N is strictly positive.", DescribeRole.Definition),
            Node("derivative", "Derivative and all three signs", "curve_derivative",
                "For every k>0,N>0 and 0<b<N/2, F is differentiable at b with the exact curveDerivative coefficient. Its derivative is negative if and only if b<N/3, zero if and only if b=N/3, and positive if and only if N/3<b.", DescribeRole.Theorem),
            Node("minimum", "The unique continuous minimum", "curve_minimum",
                "For k>0,N>0, F is strictly decreasing on (0,N/3] and strictly increasing on [N/3,N/2). At every b in (0,N/2), F(N/3)<=F(b), with equality if and only if b=N/3. The theorem proves both sides of the unique global minimum across the full scalar interval.", DescribeRole.Theorem),
            Node("boundaries", "Scalar endpoints and vacuum", "curve_boundaries",
                "For k>=0,N>0, F(k,N,0)=F(k,N,N/2)=0, with right limit zero at 0 and left limit zero at N/2. At k=0 the whole real curve is identically zero. Empty-party endpoints lie outside the three-positive-party physical theorem. No false strict vacuum derivative is asserted.", DescribeRole.Theorem),
            Node("physical", "The divisible-total physical curve", "physical_curve_minimum",
                "For every integer N>=3 divisible by 3, a>1, positive integer b with 2b<N, the actual GM3 3 (N-2b) b b a equals F(kappa(N,a),N,b). Its value is at least the actual equal-party value at (N/3,N/3,N/3), with equality if and only if b=N/3. Equivalently the multi-entropy subsystem B+C has size 2N/3. These are positive integer physical modes. For other residues the scalar continuous minimum remains valid, while no fractional-mode physical minimizer is asserted. At vacuum all admissible curve points tie by the physical vacuum theorem.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("gaussian-three-curve-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(Statement(declaration))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role, null);

    private static Formula A => Seq(Open, F.Id("N"), Minus, D(2), F.Id("b"), Close);
    private static Formula AllReals(string[] names, Formula body)
    {
        for (var i = names.Length - 1; i >= 0; --i)
            body = Seq(Forall, Sp, F.Id(names[i]), Sp, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp, body);
        return body;
    }
    private static Formula FAt(Formula b) => Seq(F.Id("F"), Open, F.Id("k"), Comma, F.Id("N"), Comma, b, Close);
    private static Formula GAt(Formula x, Formula y, Formula z) => Seq(F.Id("GM"), Underscore, D(3),
        Open, x, Comma, y, Comma, z, Comma, F.Id("a"), Close);
    private static Formula Third => Seq(Frac, Grp(F.Id("N")), Grp(D(3)));
    private static Formula Statement(string declaration) => declaration switch
    {
        "curve" => AllReals(["k", "N", "b"], Seq(FAt(F.Id("b")), Eq, F.Id("V"), Open, F.Id("k"), Comma,
            F.Id("N"), Minus, D(2), F.Id("b"), Comma, F.Id("b"), Comma, F.Id("b"), Close)),
        "curveDerivative" => AllReals(["k", "N", "b"], Seq(F.Id("D"), Open, F.Id("k"), Comma, F.Id("N"), Comma,
            F.Id("b"), Close, Eq, Frac,
            Grp(F.Id("k"), Caret, D(2), F.Id("b"), Open, D(3), F.Id("b"), Minus, F.Id("N"), Close,
                OpenBracket, F.Id("N"), Plus, F.Id("k"), Open, D(2), A, Caret, D(2), F.Id("b"),
                Plus, D(3), A, F.Id("b"), Caret, D(2), Plus, D(2), F.Id("b"), Caret, D(3), Close, CloseBracket),
            Grp(D(6), Open, D(1), Plus, D(2), F.Id("k"), F.Id("b"), A, Close,
                Open, D(1), Plus, F.Id("k"), F.Id("b"), Open, F.Id("N"), Minus, F.Id("b"), Close, Close,
                Open, D(1), Plus, F.Id("k"), Open, D(2), F.Id("N"), F.Id("b"), Minus, D(3), F.Id("b"), Caret, D(2), Close, Close))),
        "curve_derivative" => Seq(F.Id("F"), Apos, Open, F.Id("b"), Close, Eq, F.Id("D"), Semi,
            F.Id("F"), Apos, Open, F.Id("b"), Close, Lt, D(0), Sp, Iff, Sp, F.Id("b"), Lt, Third, Semi,
            F.Id("F"), Apos, Open, F.Id("b"), Close, Eq, D(0), Sp, Iff, Sp, F.Id("b"), Eq, Third, Semi,
            D(0), Lt, F.Id("F"), Apos, Open, F.Id("b"), Close, Sp, Iff, Sp, Third, Lt, F.Id("b")),
        "curve_minimum" => Seq(F.Id("StrictAntiOn"), Open, F.Id("F"), Open, F.Id("k"), Comma, F.Id("N"), Close,
            Comma, Open, D(0), Comma, Third, CloseBracket, Close, Semi,
            F.Id("StrictMonoOn"), Open, F.Id("F"), Open, F.Id("k"), Comma, F.Id("N"), Close,
            Comma, OpenBracket, Third, Comma, Frac, Grp(F.Id("N")), Grp(D(2)), Close, Close, Semi,
            FAt(Third), Le, Sp, FAt(F.Id("b")), Semi,
            FAt(F.Id("b")), Eq, FAt(Third), Sp, Iff, Sp, F.Id("b"), Eq, Third),
        "curve_boundaries" => Seq(FAt(D(0)), Eq, FAt(Seq(Frac, Grp(F.Id("N")), Grp(D(2)))), Eq, D(0), Semi,
            F.Id("F"), Open, D(0), Comma, F.Id("N"), Comma, F.Id("b"), Close, Eq, D(0), Semi,
            Lim, Underscore, Grp(F.Id("b"), To, Sp, D(0), Caret, Grp(Plus)), FAt(F.Id("b")), Eq, D(0), Semi,
            Lim, Underscore, Grp(F.Id("b"), To, Sp, Open, Frac, Grp(F.Id("N")), Grp(D(2)), Close, Caret, Grp(Minus)),
            FAt(F.Id("b")), Eq, D(0)),
        _ => Seq(F.Id("GM"), Underscore, D(3), Open, F.Id("N"), Minus, D(2), F.Id("b"), Comma,
            F.Id("b"), Comma, F.Id("b"), Comma, F.Id("a"), Close, Eq, FAt(F.Id("b")), Semi,
            GAt(Third, Third, Third), Le, Sp, GAt(Seq(F.Id("N"), Minus, D(2), F.Id("b")), F.Id("b"), F.Id("b")), Semi,
            GAt(Seq(F.Id("N"), Minus, D(2), F.Id("b")), F.Id("b"), F.Id("b")), Eq, GAt(Third, Third, Third),
            Sp, Iff, Sp, F.Id("b"), Eq, Third, Semi,
            F.Id("k"), Eq, Kappa, Open, F.Id("N"), Comma, F.Id("a"), Close, Semi,
            F.Id("b"), Eq, Third, Sp, Iff, Sp, F.Id("b"), Plus, F.Id("b"), Eq, D(2), Third)
    };
}
