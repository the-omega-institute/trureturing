using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.GaussianMultiEntropy;

internal sealed class ReplicaThreeScalarDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeScalar.";
    private static Formula V => Seq(F.Id("V"), Open, F.Id("k"), Comma, F.Id("x"), Comma,
        F.Id("y"), Comma, F.Id("z"), Close);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The order-three Gaussian expression has a symmetric scalar extension to positive real party sizes. Its logarithmic quotient is strictly negative for positive squeezing and strictly decreases as squeezing increases; at vacuum it is zero. Real coordinates in this scalar extension do not represent fractional physical modes.",
        H("Replica-three scalar expression and squeezing"),
        Blocks(
            Paragraph(Text("Scientific source: Haobo Ma then Wenlin Zhang, An exact balancing law for order-three Gaussian multi-entropy, released 4 November 2026 under CC BY 4.0. The fully symmetric physical family and equal-party observation are due to Camargo and Nishida. Classical majorization is credited to Marshall, Olkin and Arnold. The actual integral bridge belongs to the companion ReplicaThree module; the existing all-replica Fourier theorem and replica-four results retain their original scope and credits.")),
            Node("pair-sum", "The pair sum", "pairSum",
                Disp(AllReals(["x", "y", "z"], Seq(Call("s", F.Id("x"), F.Id("y"), F.Id("z")),
                    Eq, F.Id("x"), F.Id("y"), Plus, F.Id("x"), F.Id("z"), Plus, F.Id("y"), F.Id("z")))),
                "The second elementary symmetric polynomial s = xy + xz + yz of the three labelled coordinates.", DescribeRole.Definition),
            Node("cut", "A labelled cut factor", "cut",
                Disp(AllReals(["k", "x", "y", "z"], Seq(Call("D", F.Id("k"), F.Id("x"), F.Id("y"), F.Id("z")),
                    Eq, D(1), Plus, F.Id("k"), F.Id("x"), Open, F.Id("y"), Plus, F.Id("z"), Close))),
                "D_x = 1 + k x(y + z). The three factors D_x, D_y and D_z are labelled occurrences: equal numerical values are retained with multiplicity.", DescribeRole.Definition),
            Node("value", "The scalar value", "value",
                Disp(AllReals(["k", "x", "y", "z"], Seq(V, Eq, Frac,
                    Grp(D(2), Log, Open, D(1), Plus, F.Id("k"), Call("s", F.Id("x"), F.Id("y"), F.Id("z")), Close,
                        Minus, Log, Sp, Call("D", F.Id("k"), F.Id("x"), F.Id("y"), F.Id("z")),
                        Minus, Log, Sp, Call("D", F.Id("k"), F.Id("y"), F.Id("x"), F.Id("z")),
                        Minus, Log, Sp, Call("D", F.Id("k"), F.Id("z"), F.Id("x"), F.Id("y"))), Grp(D(1, 2))))),
                "V(k,x,y,z) = (2 log(1 + ks) - log D_x - log D_y - log D_z)/12, with natural logarithms. For nonnegative coordinates and k >= 0 all four logarithm arguments are positive.", DescribeRole.Definition),
            Node("swap", "Swap symmetry", "value_swap",
                Disp(Seq(V, Eq, At(F.Id("k"), F.Id("y"), F.Id("x"), F.Id("z")))),
                "For all real k,x,y,z, V(k,x,y,z)=V(k,y,x,z). Exchanging the first two party labels preserves all three cut factors with their multiplicities.", DescribeRole.Theorem),
            Node("cycle", "Cyclic symmetry", "value_cycle",
                Disp(Seq(V, Eq, At(F.Id("k"), F.Id("y"), F.Id("z"), F.Id("x")))),
                "For all real k,x,y,z, V(k,x,y,z)=V(k,y,z,x). Together with swap symmetry this gives invariance under all permutations of the three party labels, retaining every cut occurrence.", DescribeRole.Theorem),
            Node("quotient", "The logarithmic quotient", "value_eq_log_ratio",
                Disp(Seq(V, Eq, Frac, Grp(Log, Frac, Grp(Open, D(1), Plus, F.Id("k"), F.Id("s"), Close, Caret, D(2)),
                    Grp(Seq(F.Id("D"), Underscore, Grp(F.Id("x"))), Seq(F.Id("D"), Underscore, Grp(F.Id("y"))), Seq(F.Id("D"), Underscore, Grp(F.Id("z"))))), Grp(D(1, 2)))),
                "For every real k,x,y,z >= 0, the scalar value equals log((1 + ks)^2/(D_x D_y D_z))/12. Positivity justifies splitting the logarithm of the product; no cut factor is removed at ties.", DescribeRole.Theorem),
            Node("negative", "Strict negativity away from vacuum", "value_neg",
                Disp(Seq(V, Lt, D(0))),
                "For k > 0 and x,y,z > 0 the value is strictly negative. The denominator minus (1 + ks)^2 factors as k^2 xyz [N + k(Ns - xyz)], where N = x + y + z. Every factor is positive. Empty-party boundary points and k = 0 are excluded from this strict inequality.", DescribeRole.Theorem),
            Node("squeezing", "Vacuum and strict squeezing decrease", "parameter_behavior",
                Disp(Seq(F.Id("V"), Open, D(0), Comma, F.Id("x"), Comma, F.Id("y"), Comma, F.Id("z"), Close,
                    Eq, D(0), Semi, F.Id("StrictAntiOn"), Open,
                    F.Id("k"), Mapsto, Sp, V, Comma, OpenBracket, D(0), Comma, Infty, Close, Close)),
                "For every fixed x,y,z > 0, V(0,x,y,z) = 0 and k -> V(k,x,y,z) is strictly decreasing on the whole ray k >= 0. Indeed the sum of the three cut coefficients is 2s, and every cut coefficient is strictly smaller than s. For k > 0 this makes the squeezing derivative strictly negative. No negative derivative at vacuum is asserted; all triples tie there.", DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(F.Id(name), [.. args]);
    private static Formula AllReals(string[] names, Formula body)
    {
        for (var i = names.Length - 1; i >= 0; --i)
            body = Seq(Forall, Sp, F.Id(names[i]), Sp, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp, body);
        return body;
    }

    private static Formula At(Formula k, Formula x, Formula y, Formula z) =>
        Seq(F.Id("V"), Open, k, Comma, x, Comma, y, Comma, z, Close);

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("gaussian-three-scalar-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role, null);
}
