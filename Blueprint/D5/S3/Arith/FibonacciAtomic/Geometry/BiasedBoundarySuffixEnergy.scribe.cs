using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Geometry;

internal sealed class BiasedBoundarySuffixEnergyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundarySuffixEnergy.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Distinct prefix-free stopping addresses have disjoint strict-descendant coordinates in the original increment space. Their suffix energies therefore fit inside the original energy.",
        H("Disjoint Strict-Suffix Energy"), Blocks(
            Describe.Lean(DescribeId.Create("biasedboundarysuffixenergy-disjoint"),
                DeclarationHandle.Create(Prefix + "prefix_free_suffix_energy"), H("Disjoint Original Edge Coordinates"),
                StatementSource.FromAuthor(EnergyFormula()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Let A be any finite prefix-free set of original addresses and let z be any vector in the original square-summable edge space H. Then the sum over A of the squared norms of S(p)z is at most the squared norm of z. Nonempty suffixes are used throughout, so the edge ending at p is excluded.")),
                    Paragraph(Text("The map sending a pair consisting of p in A and a nonempty suffix u to the original edge pu is injective. If two such edges agreed, their prefixes would be comparable; prefix freedom would force the prefixes to agree, and cancellation would force the suffixes to agree. The resulting subseries of the nonnegative squared edge coordinates is bounded by the complete energy series. This argument applies directly to every z in H."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("biasedboundarysuffixenergy-weighted"),
                DeclarationHandle.Create(Prefix + "weighted_centered_suffix_energy"), H("Weighted Actual Centered Suffixes"),
                StatementSource.FromAuthor(WeightedFormula()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Suppose t is nonnegative and each weight w(p), for p in A, lies between zero and t. For the actual centered trace C on the original biased boundary, the sum of w(p) times the squared norm of C(S(p)z) is at most the golden ratio times t times the squared norm of z.")),
                    Paragraph(Text("Apply the actual conditional centering identity and its Hardy estimate to each suffix, use w(p) at most t, and then apply the disjoint strict-suffix energy estimate. The weights can be actual cylinder masses whenever their threshold bound has been established.")),
                    Paragraph(Text("This estimate supplies the suffix-energy inequalities in a stopping argument. Identifying this weighted sum with the norm of the global atom-average residual requires the actual cylinder projection and its conditional norm decomposition. No assertion about the covariance or the spectral counting function follows here alone."))), DescribeRole.Theorem))));
    private static Formula V(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(Seq(Operatorname, Grp(V(s))), [.. xs]);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula SqNorm(Formula x) => Seq(Par(Seq(Vert, Sp, x, Vert)), Caret, Grp(D(2)));
    private static Formula SumA(Formula x) => Seq(Sum, Underscore, Grp(Seq(V("p"), InMacro, Sp, V("A"))), Sp, Par(x));
    private static Formula All(string s, Formula t, Formula x) => Seq(Forall, Sp, V(s), Colon, Sp, t, Comma, Sp, Par(x));
    private static Formula EnergyFormula() => All("A",Call("Finset",Call("Address")),All("z",Call("H"),Seq(
        Call("IsPrefixFree", V("A")), Implies, Sp,
        SumA(SqNorm(Call("S", V("p"), V("z")))), Leq, Sp, SqNorm(V("z")))));
    private static Formula WeightedFormula() => All("A",Call("Finset",Call("Address")),
        All("w",Seq(Call("Address"),To,Sp,Call("Real")),All("t",Call("Real"),All("z",Call("H"),Seq(
        D(0), Leq, Sp, V("t"), Land, Sp, Call("IsPrefixFree", V("A")), Land, Sp,
        Par(Seq(Forall, Sp, V("p"), InMacro, Sp, V("A"), Comma, Sp, D(0), Leq, Sp, Call("w", V("p")), Leq, Sp, V("t"))), Implies, Sp,
        SumA(Seq(Call("w", V("p")), Cdot, Sp, SqNorm(Call("C", Call("S", V("p"), V("z")))))), Leq, Sp,
        Call("goldenRatio"), Cdot, Sp, V("t"), Cdot, Sp, SqNorm(V("z")))))));
}
