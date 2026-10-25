using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.StoneCech;

internal sealed class HistoricalFilterCollisionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/StoneCech/HistoricalFilterCollision.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All historical sets determine a fixed distinct free pair; separate historical convergence of each continuous observable forces their images to coincide.",
        H("Historical filters and fixed free collisions"),
        Blocks(
            Paragraph(Text(
                "The primary application is the CH signed Talagrand history: I is the type of all proper ordinal tail stages, J(i) is the actual historical set, "
                + "and N0,N1 are the two original disjoint birth reservoirs. Later stages refine earlier sets modulo finite exceptions, and every historical J(i) "
                + "meets both original reservoirs infinitely. These facts are inputs here. The theorem imposes no countability on I and chooses no final J or common infinite pseudointersection.")),
            Describe.Lean(
                DescribeId.Create("fixed-free-historical-pair"),
                DeclarationHandle.Create(Owner + "exists_distinct_free_ultrafilters"),
                H("Two free extensions of the entire history"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Topology/kania2026talagrand")),
                Blocks(
                    Paragraph(Text(
                        "Let I be any nonempty type, J:I -> Set Nat, and suppose that for every i,j there is k for which J(k) minus J(i) and J(k) minus J(j) are finite. "
                        + "Let N0,N1 be disjoint, with J(i) intersect N0 and J(i) intersect N1 infinite for every i. Then there exist u0,u1:Ultrafilter Nat "
                        + "with both underlying filters below cofinite, N0 in u0, N1 in u1, every J(i) in both ultrafilters, and u0 distinct from u1. "
                        + "The filter order reverses inclusion of collections of sets; below cofinite therefore means free, or nonprincipal, on Nat.")),
                    Paragraph(Text(
                        "For each reservoir N use F(i)=cofinite inf principal(J(i) intersect N). Removing a finite difference leaves this filter unchanged, "
                        + "so a common refinement modulo finite exceptions refines both filters. Infinitude makes each F(i) nonbottom, and directedness makes their infimum nonbottom. "
                        + "Ultrafilter.of extends this actual infimum. Nonemptiness of I recovers cofinite and N membership, while each index separately gives J(i) membership. "
                        + "Two extensions cannot agree because a proper filter cannot contain both disjoint reservoirs.")),
                    Paragraph(Text(
                        "This is a repository composition of classical filter facts. The precise upstream sources are Mathlib.Order.Filter.Cofinite, "
                        + "especially Set.Finite.cofinite_inf_principal_sdiff and cofinite_inf_principal_neBot_iff, Filter.iInf_neBot_of_directed', "
                        + "and Mathlib.Order.Filter.Ultrafilter.Basic with Ultrafilter.of and Ultrafilter.of_le. The ultrafilter lemma is classical and choice is used; "
                        + "no effective enumeration of the pair is claimed. FreeUltrafilterCardinality supplies the nearby project example of the directed-filter extension method, "
                        + "but no cardinal-supply theorem is needed as a mathematical dependency."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("historical-observable-collision"),
                DeclarationHandle.Create(Owner + "eq_of_historical_observables"),
                H("Observable-specific stages force equality of fixed images"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Topology/kania2026talagrand")),
                Blocks(
                    Paragraph(Text(
                        "Fix any u0,u1 below cofinite and containing every J(i). Let V:Ultrafilter Nat -> X be continuous. "
                        + "Let phi(a):X -> Y(a) be continuous, with every Y(a) Hausdorff, and let the whole family separate points of X. "
                        + "For every a assume there are i and L such that n |-> phi(a)(V(pure n)) tends to L along cofinite inf principal(J(i)). "
                        + "Then V(u0)=V(u1). The spaces Y(a) may depend on a; neither a common historical index nor Hausdorffness of X is an extra assumption.")),
                    Paragraph(Text(
                        "Membership in J(i) and freeness put each chosen ultrafilter below the filter on which this one observable converges. "
                        + "Hence the same sequence converges to L along each ultrafilter. In the actual compact Hausdorff topology on Ultrafilter Nat, "
                        + "Mathlib's Ultrafilter.tendsto_pure_self says pure tends along u to u. Continuity of phi(a) composed with V therefore gives the second limit phi(a)(V(u)). "
                        + "Hausdorff uniqueness identifies these two limits. Equality for every a and point separation give equality in X. "
                        + "This uses actual continuous V, without any supplied ultrafilter-extension evaluation identity.")),
                    Paragraph(Text(
                        "Choose the pair from the first theorem once, before choosing any observable. In the signed-ball application, X is the final weak-star target and "
                        + "phi(g) is evaluation at a continuous test function g. Each test may reflect to its own proper ordinal stage and converge on its own J(i). "
                        + "The same fixed distinct free pair then has equal V images. These free points are precisely the type required by a later signed-ball perturbation argument; "
                        + "a collision involving a principal point is not substituted.")),
                    Paragraph(Text(
                        "The exact statements are repository-derived compositions of the classical ultrafilter lemma, continuity and uniqueness of Hausdorff limits. "
                        + "The Kania-Kakol Library reference records the original Talagrand question and is contextual attribution, not attribution of these exact generic statements. "
                        + "No mathematical novelty, completed CH recursion, final signed-ball contradiction, full solution or official acceptance is claimed. "
                        + "The actual history, its infinite reservoir intersections, continuity and separating tests must be supplied by their own constructions. "
                        + "All declarations are general structural mathematics, so utility is none: there is no bounded enumeration, numerical certificate or certified finite instance."))),
                DescribeRole.Theorem))));
}
