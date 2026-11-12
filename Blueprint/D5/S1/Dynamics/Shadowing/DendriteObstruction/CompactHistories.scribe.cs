using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing.DendriteObstruction;

internal sealed class DendriteObstructionCompactHistoriesDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Shadowing/DendriteObstruction/CompactHistories.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual compact histories and maximal attained fibre multiplicity.",
        H("DendriteObstruction - Compact histories"), Blocks(
        Describe.Lean(DescribeId.Create("exists-iterate-injective-arc"),
            DeclarationHandle.Create(Owner + "exists_iterate_injective_arc"),
            H("An embedded arc with all iterates injective"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(
                Paragraph(Text("Let X be a compact metric space containing an actual embedded nondegenerate closed interval. Assume every continuous map from AddCircle (1 : Real) to X fails to be injective. Assume also the purely static arc-hull law: for any distinct endpoints p,y, some embedded arc from p to y lies in every compact connected subset containing both endpoints. If a continuous self-map f is finitely positively expansive, there is an actual embedded nondegenerate arc K such that f^[n] is injective on K for every natural n, including zero.")),
                Paragraph(Text("A compact history consists of a nonempty compact source E, an actual terminal arc K, a time t, strict distance bounds at every time j <= t, exact image f^[t](E)=K, and a uniform lower bound r for every terminal fibre inside E. A small affine subarc initializes r=1. Each attainable r is bounded by the fixed all-time Bowen cardinal bound: a terminal fibre has controlled prefix and exactly coalescing tail. A finite maximum is therefore attained by actual history data.")),
                Paragraph(Text("A noninjective iterate on the attained terminal arc yields an arbitrarily short repeated pair by ShortLoops.short_repeated_pair_finite_prefix. Finite iterate fibres prohibit collapse of the entire loop interval and give a distinct interior image y. The static hull arc from the repeated value p to y lies in both half-path images. Its first half B excludes y. Intersecting the complete left and right source halves with the inverse image of B gives disjoint compact sets P and Q, each with exact image B; these sets are allowed to be disconnected. Restricting E to the complete inverse image of P union Q retains every old fibre. The two distinct intermediate fibres are disjoint and their cardinal lower bounds add, giving 2r at time t+q. Old prefix times follow from source inclusion; all new times t+j follow from the short-loop prefix bound. This contradicts maximality.")),
                Paragraph(Text("This is a conditional dynamical core. StaticArcHull and the no-circle predicate are explicit intermediate assumptions, not a compiled identification of all dendrites or all dendroids. It does not yet exclude finite positive expansivity by itself. The full obstruction additionally needs derived uniform dynamical persistence and a static uniform bound for disjoint large subarcs, followed by a compiled bridge from the intended carrier. Analytic Pro advice is fallible; no model independence or diversity is asserted."))), DescribeRole.Theorem))));
}
