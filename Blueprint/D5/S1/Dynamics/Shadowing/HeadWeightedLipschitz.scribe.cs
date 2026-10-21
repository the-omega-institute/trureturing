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
        "Lipschitz shadowing of a uniformly bounded head-weight full shift is equivalent to a cross-head adjacent-depth ratio bound.",
        H("An Exact Head-Weight Criterion for Lipschitz Shadowing"),
        Blocks(
            Paragraph(Text("This theorem resumes the repository's October 14 ordinary classification derivation for the complete HeadWeights family. The earlier concrete counterexample answers the unrestricted metric-change question of Goncalves and Silva, arXiv:2603.03200v1, negatively; the present result explains the exact quantitative boundary within that family. It is a repository deduction, not a second open-problem solution count or a classification of arbitrary compatible metrics.")),
            Describe.Lean(
                DescribeId.Create("head-adjacent-ratio-classification"),
                DeclarationHandle.Create("D5/S1/Dynamics/Shadowing/HeadWeightedLipschitz.metric_hasLipschitzShadowing_iff_adjacent_ratio"),
                H("The exact cross-head criterion"),
                StatementSource.FromAuthor(Disp(new Formula.Aligned([
                    Seq(Forall, Sp, Id("w"), Colon, Sp, Call("HeadWeights"), Comma, Sp,
                        Forall, Sp, Id("b"), Colon, Sp, Call("UniformBounds", Id("w")), Comma),
                    Seq(Call("HasLipschitzShadowing", Call("metric", Id("b")), Call("shift", D(1))),
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
                    Paragraph(Text("For necessity, write L and c for proposed Lipschitz constants and choose K with upper(K)<c/2. Set C=max(2L,1/lower(K)). At depths n-1<=K, the positive lower bound makes every ratio at most C. At larger depths a violation gives two distinct heads and a single-defect infinite pseudo-orbit with error 2 weight(t,n-1)<=c. Time zero forces the tracer to retain the old symbol at position n, while time n requires the inserted symbol; their heads then have distance one. The existing exact defect supplier makes this contradiction global in time.")),
                    Paragraph(Text("HeadWeightedMetric supplies the metric, product uniformity, prefix controls and defect family; MetricTracing supplies diagonal_mismatch_edge. The cross-head iff is new formal content relative to those suppliers. Necessity and sufficiency concern only this head-weight family. No locally compact assertion, arbitrary-metric classification, current global uniqueness or official external acceptance is asserted. The retained Reg mirror preserves both original telescopes and records unresolved registration issue #5214."))),
                DescribeRole.Theorem))));
}
