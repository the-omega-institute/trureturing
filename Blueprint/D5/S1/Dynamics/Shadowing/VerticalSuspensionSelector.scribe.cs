using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class VerticalSuspensionSelectorDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Shadowing/VerticalSuspensionSelector.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The compact locally equiconnected vertical suspension has a continuous full integer selector for every compatible metric.",
        H("Full Integer Crossing Selector on the Actual Suspension"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("compact-lec-crossing-selector"),
                DeclarationHandle.Create(Owner + "compact_lec_crossing_selector"),
                H("Every compatible metric and every sufficiently small closed tolerance"),
                StatementSource.FromAuthor(Seq(
                    Forall, Sp, F.Id("K"), Comma, Sp,
                    F.Id("CompactMetrizableNonempty"), Open, F.Id("K"), Close, Sp, Rightarrow, Sp,
                    Forall, Sp, F.Id("H"), Colon, Sp,
                    F.Id("LocalEquiconnection"), Open, F.Id("K"), Close, Comma, Sp,
                    Forall, Sp, F.Id("d"), Colon, Sp, F.Id("CompatibleMetric"),
                    Open, F.Id("Suspension"), Open, F.Id("K"), Close, Close, Comma, Sp,
                    Exists, Sp, F.Id("deltaStar"), Gt, D(0), Comma, Sp,
                    Exists, Sp, F.Id("Rstar"), Colon, Sp, F.Id("IntegerSelector"),
                    Open, F.Id("vertical"), Comma, F.Id("deltaStar"), Close, Comma, Sp,
                    Forall, Sp, F.Id("delta"), Comma, Sp,
                    Open, D(0), Lt, F.Id("delta"), Sp, Land, Sp,
                    F.Id("delta"), Le, F.Id("deltaStar"), Close, Sp, Rightarrow, Sp,
                    Exists, Sp, F.Id("R"), Colon, Sp, F.Id("IntegerSelector"),
                    Open, F.Id("vertical"), Comma, F.Id("delta"), Close, Comma, Sp,
                    Forall, Sp, F.Id("x"), InMacro, F.Id("ClosedPseudoOrbit"),
                    Open, F.Id("vertical"), Comma, F.Id("delta"), Close, Comma, Sp,
                    F.Id("R"), Open, F.Id("x"), Close, Eq,
                    F.Id("Rstar"), Open, F.Id("inclusion"), Open, F.Id("x"), Close, Close)),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "K is an arbitrary nonempty compact metrizable space. A single continuous "
                        + "H:W×[0,1]→K is given on an open neighborhood W of the diagonal in K×K, "
                        + "with H(u,v,0)=u, H(u,v,1)=v and H(u,u,s)=u. No ANR, finite dimension, "
                        + "connectedness, symmetry or higher arity assumption is made.")),
                    Paragraph(Text(
                        "The carrier M is the native quotient of K×[-1,1]: two representatives "
                        + "agree precisely when their heights agree and either that height is -1, "
                        + "that height is 1, or their K-labels agree. The two end faces collapse "
                        + "separately. Its topology is the quotient topology. The theorem quantifies "
                        + "over every metric d inducing exactly that topology, using replaceTopology "
                        + "with the explicit topology equality. The vertical homeomorphism is "
                        + "f(q(u,v))=q(u,(v+c)/(1+cv)), c=tanh(1), and has all integer powers.")),
                    Paragraph(Text(
                        "Pδ is the subtype of ALL functions x:ℤ→M satisfying "
                        + "d(f(x(j)),x(j+1))≤δ for EVERY integer j, with the full product subspace "
                        + "topology. It is closed. Translation by n is an actual homeomorphism of "
                        + "this same domain and is proved to equal σ^n for σ=shift(1). "
                        + "IntegerSelector requires a continuous map R:Pδ→M, "
                        + "R(orb(z))=z for every z, and R(σ^n(x))=f^n(R(x)) for every integer "
                        + "n and every x. All negative times and errors equal to δ are retained.")),
                    Paragraph(Text(
                        "There is δstar>0 and such an Rstar on Pδstar. For every 0<δ≤δstar, "
                        + "the theorem also supplies an IntegerSelector on Pδ whose map is "
                        + "literally Rstar composed with the natural subtype inclusion. Thus all "
                        + "smaller tolerances use one formula. No quantitative shadowing estimate "
                        + "is asserted beyond this exact selector contract.")),
                    Paragraph(Text(
                        "The formula locates a weak crossing j with v(j)≤0≤v(j+1), where "
                        + "v(j)=height(x(j)). Put A=artanh(v(j)), B=artanh(v(j+1)), "
                        + "s=-A/(B-A) and T=-j-s. The output is q(H(L(x(j)),L(x(j+1)),s),tanh(T)). "
                        + "Compact bad-pair separation gives the sign rule and the W/interior "
                        + "checks at every admitted link. The sign rule makes B-A positive and "
                        + "s lie in [0,1]. Different crossings are adjacent at a zero height; "
                        + "the connector endpoint identities make their outputs exactly equal.")),
                    Paragraph(Text(
                        "Every all-negative history maps to the lower pole and every all-positive "
                        + "history to the upper pole. At a crossing, a finite closed cover in a "
                        + "strict-sign neighborhood proves continuity. At an arbitrary strict-sign "
                        + "history, the compact tube lemma supplies label-uniform pole neighborhoods; "
                        + "one far coordinate bounds every crossing phase in that neighborhood. "
                        + "This includes arbitrary nonconstant strict-sign histories and makes no "
                        + "tail-convergence or local-finiteness assumption at a pole class.")),
                    Paragraph(Text(
                        "The crossing construction and the arctanh interpolation are attributed "
                        + "to the supplied Pro author formula and its independently reviewed public "
                        + "source proof. The formal implementation reuses pinned Mathlib artanh, "
                        + "quotient topology, compact extrema, compact tubes and finite pasting. "
                        + "This is a substantive intermediate selector theorem. It proves neither "
                        + "the necessity of LEC nor compact LEC implies ANR, and claims no "
                        + "literature novelty or official acceptance."))),
                DescribeRole.Theorem))));
}
