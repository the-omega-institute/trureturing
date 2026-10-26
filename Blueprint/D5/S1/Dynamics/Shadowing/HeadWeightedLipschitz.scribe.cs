using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class HeadWeightedLipschitzDocument : IScribeDocumentDefinition
{
    private static Formula Id(string s) => F.Id(s);
    private static Formula Nat => Seq(Mathbb, Grp(Id("N")));
    private static Formula Real => Seq(Mathbb, Grp(Id("R")));
    private static Formula Call(string s, params Formula[] args)
    {
        var items = new List<Formula> { Seq(Operatorname, Grp(Id(s))), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Lipschitz shadowing for every normalized positive nonincreasing head-weight full shift is equivalent to a cross-head adjacent-depth ratio bound.",
        H("An Exact Head-Weight Criterion for Lipschitz Shadowing"),
        Blocks(
            Paragraph(Text("On a countable alphabet, prefix weights may depend on the initial symbol. The theorem gives an exact Lipschitz shadowing criterion for every normalized positive nonincreasing family of those weights. Uniform upper and lower envelopes are unnecessary. The existing counterexample answers the unrestricted metric-change question of Goncalves and Silva, arXiv:2603.03200v1, negatively; this result explains the quantitative boundary within its head-weight family.")),
            Describe.Lean(
                DescribeId.Create("head-adjacent-ratio-classification"),
                DeclarationHandle.Create("D5/S1/Dynamics/Shadowing/HeadWeightedLipschitz.rawMetric_hasLipschitzShadowing_iff_adjacent_ratio"),
                H("The exact cross-head criterion"),
                StatementSource.FromAuthor(Disp(new Formula.Aligned([
                    Seq(Forall, Sp, Id("w"), Colon, Sp, Call("HeadWeights"), Comma),
                    Seq(Call("HasLipschitzShadowing", Call("rawMetric", Id("w")), Call("shift", D(1))),
                        Sp, Iff, Sp, Exists, Sp, Id("C"), Colon, Sp, Real, Comma, Sp,
                        D(0), Sp, Lt, Sp, Id("C"), Sp, Land),
                    Seq(Forall, Sp, Id("s"), Sp, Id("t"), Sp, Id("n"), Colon, Sp, Nat, Comma, Sp,
                        D(1), Sp, Le, Sp, Id("n"), Sp, Rightarrow, Sp,
                        Call("weight", Id("w"), Id("s"), Id("n")), Sp, Le, Sp,
                        Id("C"), Call("weight", Id("w"), Id("t"), Seq(Id("n"), Minus, D(1))))
                ]))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Topology/goncalvessilva2026shadowing")),
                Blocks(
                    Paragraph(Text("For sufficiency, use the actual infinite diagonal splice. A tracing mismatch at depth n telescopes to an edge mismatch at depth m<=n-1. The cross-head comparison followed by antitonicity bounds the tracing error by C times that strict edge error, at every natural time. This supplies constant C and cutoff one, with all symbols and infinite pseudo-orbits quantified.")),
                    Paragraph(Text("For necessity, let L and c be proposed positive Lipschitz controls and set C=max(2L,max(2/c,1)). Every weight is at most one, so a violating ratio, with e=weight(t,n-1), gives Ce<1 and hence 2e<c. Depth one and equal heads cannot violate the bound. The existing single-defect infinite pseudo-orbit has strict edge errors below delta=2e and permits no full tracer at radius L delta<=Ce<weight(s,n). Time zero forces the old symbol at position n, while time n forces the inserted symbol. This contradiction establishes necessity without any common tail decay hypothesis.")),
                    Paragraph(Text("When UniformBounds are available, HeadWeightedMetric replaces the metric uniformity by the standard product uniformity while keeping exactly the same distance. The theorem therefore gives the same criterion for that compatible product metric. The constant weight family has the discrete metric and is also covered, although it has no uniformly vanishing upper envelope. Thus the raw-metric statement extends beyond the product-uniform subclass.")),
                    Paragraph(Text("HeadWeightedMetric supplies the metric, prefix controls and exact infinite defect family; MetricTracing supplies diagonal_mismatch_edge. The cross-head iff is repository-derived content relative to those suppliers. It does not count the existing metric counterexample again or assert a classification of arbitrary compatible metrics, the locally compact variant, publication priority or official external acceptance."))),
                DescribeRole.Theorem))));
}
