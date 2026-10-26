using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic;

internal sealed class PrefixGrowthEntropyDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Symbolic/PrefixGrowthEntropy.";
    private static Formula Id(string s) => F.Id(s);
    private static Formula Nat => Seq(Mathbb, Grp(Id("N")));
    private static Formula Real => Seq(Mathbb, Grp(Id("R")));
    private static Formula Call(string s, params Formula[] args)
    {
        var name = new List<Formula>();
        foreach (var part in s.Split('.'))
        {
            if (name.Count > 0) name.Add(Dot);
            name.Add(Id(part));
        }
        var items = new List<Formula> { Seq(Operatorname, Grp(Seq([.. name]))), Open };
        for (var i = 0; i < args.Length; i++) { if (i > 0) items.AddRange([Comma, Sp]); items.Add(args[i]); }
        items.Add(Close); return Seq([.. items]);
    }
    private static Formula All(string s, Formula t) => Seq(Forall, Sp, Id(s), Colon, Sp, t, Comma);
    private static Formula St(params Formula[] lines) => Disp(new Formula.Aligned([.. lines]));
    private static Formula Sequences => Seq(Nat, Sp, To, Sp, Id("A"));
    private static Formula Shift => Call("FullShift.shift", D(1));
    private static Formula Instance(string name) => Seq(OpenBracket, Call(name, Id("A")), CloseBracket);
    private static Formula PrefixMap => Seq(Open, Id("x"), Colon, Sp, Id("S"), Sp, Mapsto, Sp,
        Open, Id("i"), Colon, Sp, Call("Fin", Id("n")), Sp, Mapsto, Sp,
        Call("x", Call("Fin.val", Id("i"))), Close, Close);
    private static Formula LogRate => Seq(Open, Id("n"), Colon, Sp, Nat, Sp, Mapsto, Sp,
        Call("Real.log", Seq(Call("prefixCount", Id("S"), Id("n")), Colon, Sp, Real)),
        Slash, Id("n"), Close);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual prefix counts have a real logarithmic growth limit equal to the covering entropy of any nonempty forward-invariant symbolic set.",
        H("Prefix Growth and Symbolic Entropy"), Blocks(
        Paragraph(Text("Let A be a finite alphabet with discrete uniformity and let S be a nonempty subset of the one-sided full shift A^N. "
            + "The map T is SymbolicDynamics.FullShift.shift(1): T(x)(j)=x(1+j). Forward invariance means T(S) is contained in S. "
            + "No closedness, compactness of S, surjectivity, shadowing property or graph presentation is assumed. "
            + "This is the classical word-growth formula for symbolic entropy; the contribution here is the formal bridge to Mathlib's covering entropy, without a literature novelty claim.")),
        Describe.Lean(DescribeId.Create("actual-prefix-count"), DeclarationHandle.Create(Owner + "prefixCount"),
            H("Count realized prefixes"), StatementSource.FromAuthor(St(
                All("A", Id("Type")), All("S", Call("Set", Sequences)), All("n", Nat),
                Seq(Call("prefixCount", Id("S"), Id("n")), Sp, Eq, Sp,
                    Call("Nat.card", Call("Set.range", PrefixMap))))),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("prefixCount(S,n) is Nat.card of the range of x in S mapped to the function i in Fin(n) ↦ x(i.val). "
                + "It counts prefixes actually realized by elements of S. The empty prefix has one realization class because S is nonempty. "
                + "Finite alphabet cardinality gives prefixCount(S,n) at most card(A)^n, and forward invariance lets a realized prefix of length m+n split into realized prefixes of lengths m and n."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("prefix-growth-entropy"), DeclarationHandle.Create(Owner + "prefix_growth_entropy"),
            H("The real growth limit computes covering entropy"), StatementSource.FromAuthor(St(
                All("A", Id("Type")), Seq(Grp(), Instance("Fintype"), Sp, Instance("UniformSpace"), Sp,
                    Instance("DiscreteUniformity"), Comma),
                All("S", Call("Set", Sequences)),
                Seq(Call("Nonempty", Id("S")), Sp, Land, Sp, Call("MapsTo", Shift, Id("S"), Id("S")), Sp, Rightarrow),
                Seq(Exists, Sp, Id("h"), Colon, Sp, Real, Comma),
                Seq(D(0), Sp, Le, Sp, Id("h"), Sp, Land, Sp, Id("h"), Sp, Le, Sp,
                    Call("Real.log", Call("Fintype.card", Id("A"))), Sp, Land),
                Seq(Call("Tendsto", LogRate, Id("atTop"), Call("nhds", Id("h"))), Sp, Land),
                Seq(Call("coverEntropy", Shift, Id("S")), Sp, Eq, Sp, Call("coeEReal", Id("h"))))),
            AssessedProvenance.FromRepo(), Blocks(
                Paragraph(Text("The rate prefixLogRate(S)(n) is Real.log(prefixCount(S,n))/n; its value at n=0 uses Lean's real division convention. "
                    + "The theorem gives an actual real limit h with 0≤h≤log(card A), and identifies Mathlib Dynamics.coverEntropy(T,S) with h embedded into EReal.")),
                Paragraph(Text("For the entourage U_k of agreement on the first k coordinates, k,n>0, the dynamical entourage over times 0 through n-1 is exactly agreement on n+k-1 coordinates. "
                    + "Its minimum covering cardinality is exactly prefixCount(S,n+k-1). One actual representative per realized prefix supplies a cover. "
                    + "Conversely any ambient center can cover at most one realized prefix class, so choosing a covering center for each class is injective. "
                    + "Mathlib allows centers in the ambient full shift; the lower bound accounts for this convention.")),
                Paragraph(Text("Splitting prefixes proves submultiplicativity of their counts. Taking logarithms and applying Mathlib's Subadditive.tendsto_lim yields the real limit. "
                    + "Adding a fixed prefix width preserves the logarithmic rate. The prefix agreement entourages belong to and are cofinal in the product uniformity, "
                    + "so their common exponential covering growth is the full covering entropy. The proof reuses D5.S1.Dynamics.Shadowing.MetricTracing.shift_one_iterate_apply and Mathlib's dynamical covers, uniformity, exponential growth and Fekete lemma."))),
            DescribeRole.Theorem))));
}
