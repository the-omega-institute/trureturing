using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.GaussianMultiEntropy;

internal sealed class ReplicaThreeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThree.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every positive integer tripartition of the actual fully symmetric pure real Gaussian state, the integral-defined genuine multi-entropy at replica order three has an exact logarithmic formula. The spectrum and the three cut factors retain party multiplicity, including all tied party sizes and vacuum.",
        H("The actual Gaussian integral at replica order three"),
        Blocks(
            Paragraph(Text("The scientific source is An exact balancing law for order-three Gaussian multi-entropy by Haobo Ma then Wenlin Zhang, released 4 November 2026 under CC BY 4.0. Camargo and Nishida supply the physical family and equal-party observation. The actual all-replica Fourier and positivity bridge is the prior ResidualLimit.GM3_eq_fourierGM theorem. The Gaussian integration foundation retains Mario Brcic's Apache-2.0 transplant attribution at upstream commit 254b6275b753efb609cd38ef4c85eef29b4a13b4. This order-three result does not claim the existing all-n bridge or replica-four product as new work; ReplicaFour's specialized constants and remainders concern (m,1,1).")),
            Node("parameter", "The order-three parameter", "kappa",
                Disp(Seq(Forall, Sp, F.Id("N"), Comma, F.Id("a"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp, Kappa, Open, F.Id("N"), Comma, F.Id("a"), Close, Eq, Frac, Grp(D(3), Open, F.Id("a"), Caret, D(2), Minus, D(1), Close),
                    Grp(D(4), Open, F.Id("N"), Minus, D(1), Close))),
                "kappa(N,a) = 3(a^2 - 1)/(4(N - 1)), three quarters of the library's squeezing parameter (a^2 - 1)/(N - 1). For physical mode counts N >= 3 and a >= 1 it is nonnegative, and for a > 1 it is positive.", DescribeRole.Definition),
            Node("closed", "The integral-defined closed formula", "GM3_three_closed",
                Disp(Seq(F.Id("GM"), Underscore, Grp(D(3)), Eq, Frac, Grp(Log, Frac,
                    Grp(Open, D(1), Plus, Kappa, Sp, F.Id("s"), Close, Caret, D(2)),
                    Grp(Seq(F.Id("D"), Underscore, Grp(F.Id("x"))), Seq(F.Id("D"), Underscore, Grp(F.Id("y"))), Seq(F.Id("D"), Underscore, Grp(F.Id("z"))))), Grp(D(1, 2)))),
                "For every positive integer x,y,z and real a >= 1, let N = x + y + z, s = xy + xz + yz, and D_u = 1 + kappa u(N - u). The actual GaussianMultiEntropyAsymptotic.GM3 3 x y z a equals log((1 + kappa s)^2/(D_x D_y D_z))/12. This is the real eMinus fully symmetric pure bosonic Gaussian family, with the original Lebesgue replica integrals, twists and entropy normalizations. At replica three the nine tripartite weights consist of zero, two occurrences of each labelled cut coefficient multiplied by 3/4, and two occurrences of 3s/4. The existing all-n integral/Fourier bridge and positive products justify the logarithmic reduction. All ties and permutations are in scope. Real party sizes in the scalar supplier are a scalar extension only. Replica-one continuation, higher-replica balancing, other Gaussian branches and large-N/Page asymptotics remain separate; fixed-a Page/large-N asymptotics have a separate range.", DescribeRole.Theorem),
            Node("behavior", "Physical vacuum and squeezing", "GM3_three_behavior",
                Disp(Seq(GAt(D(1)), Eq, D(0), Semi,
                    F.Id("StrictAntiOn"), Open, F.Id("a"), Mapsto, Sp, GAt(F.Id("a")),
                    Comma, OpenBracket, D(1), Comma, Infty, Close, Close, Semi,
                    Forall, Sp, F.Id("a"), Gt, D(1), Comma, GAt(F.Id("a")), Lt, D(0))),
                "For every positive integer x,y,z, the actual integral-defined replica-three value is zero at a = 1, strictly decreasing on a >= 1, and strictly negative at every a > 1. The parameter kappa is strictly increasing in a on this physical ray and vanishes at vacuum. Every positive integer triple therefore ties at vacuum. No strictly negative derivative at a = 1 and no extension to fractional physical mode counts is asserted.", DescribeRole.Theorem))));

    private static Formula GAt(Formula a) => Seq(F.Id("GM"), Underscore, Grp(D(3)),
        Open, F.Id("x"), Comma, F.Id("y"), Comma, F.Id("z"), Comma, a, Close);

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("gaussian-three-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role, null);
}
