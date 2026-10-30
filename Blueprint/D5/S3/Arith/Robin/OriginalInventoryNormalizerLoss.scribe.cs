using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class OriginalInventoryNormalizerLossDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete original inventory growth controls the omitted length and literal kernel mass.",
        H("Original Inventory and Normalizer Loss"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("original-inventory-normalizer-loss"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/OriginalInventoryNormalizerLoss.original_inventory_normalizer_loss"),
                H("Every original label, both collars, and the complete selected normalizer"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let X be the original full-domain attained window. Enumerate every label "
                        + "by a strictly increasing p:Fin(n+1)->Nat with X.labels=univ.image(p), "
                        + "and require X.labels=originalLabelWindow(ell), the complete literal "
                        + "prime window at ell. Put N_i=canonicalSource(p_i), T_i=log(N_i), "
                        + "and U_i=N_i/p_i using natural division. Assume 243<=ell, "
                        + "ell<=T_i<=R for every label, and R<p_0. These all-source clock "
                        + "bounds are stronger than bounds only on edges already selected.")),
                    Paragraph(Text(
                        "The conclusion derives strict clock order, N_i=p_i U_i, positive "
                        + "inventories retaining 5040, and adjacent divisibility U_i|U_(i+1). "
                        + "An adjacent pair satisfies the original GoodEdge predicate if and "
                        + "only if its inventories agree. Thus the actual selectedDomain(X), "
                        + "with every qualifying edge retained, is exactly the union of the "
                        + "closed intervals [T_i,T_(i+1)] over equal-inventory adjacent pairs. "
                        + "The full closed strict inventory condition, including both endpoints, "
                        + "comes from original_prime_source_order applied to actual full "
                        + "positive-integer maximizing sources; it is not an assumption.")),
                    Paragraph(Text(
                        "Let bad={i<n:U_i!=U_(i+1)}, D=log(U_n)-log(U_0), and "
                        + "C=(T_0-ell)+(R-T_n). For J=[ell,R] and S=selectedDomain(X), "
                        + "volume(J minus S)=C+sum_bad(T_(i+1)-T_i)<=C+2D. Completeness "
                        + "of the prime window rules out any ordinary prime between adjacent "
                        + "labels. Bertrand bounds their ratio by two. A strict change in a "
                        + "positive integer divisibility chain increases the inventory by at "
                        + "least two. The existing inventory_gap_log_bound therefore pays "
                        + "each omitted source interval by twice its logarithmic inventory "
                        + "increment; equal-inventory increments vanish, and the sum telescopes.")),
                    Paragraph(Text(
                        "For every real x the exact mass identity is windowMass(ell,R,x) "
                        + "minus integral_S kernel(t,x) = windowMass(ell,T_0,x) "
                        + "+ sum_bad windowMass(T_i,T_(i+1),x) + windowMass(T_n,R,x). "
                        + "This difference lies between zero and ell^(-3/10)(C+2D). "
                        + "The kernel and windowMass are exactly those of OriginalMovingWindowMoment "
                        + "and OriginalMovingCutRow. Their existing height and positivity bounds "
                        + "supply 0<=kernel(t,x)<=t^(-3/10)<=ell^(-3/10). No division, "
                        + "positive normalizer, or assumed normalizer comparison is used.")),
                    Paragraph(Text(
                        "Shared endpoints are removed only up to null sets: selected closed "
                        + "cells have the same integrals as their disjoint half-open cells. "
                        + "Integrating an arbitrary integrable function gives the collar and "
                        + "cell partition; applying it to one yields the exact omitted length, "
                        + "and applying it to the literal kernel yields the exact mass identity. "
                        + "For n=0 there are no edges, S is empty, D=0 and both collars cover "
                        + "the reference interval in measure. The enumeration premise explicitly "
                        + "excludes an empty label set. For empty labels goodEdges and S are "
                        + "empty directly by their definitions, and the loss is the entire "
                        + "windowMass; T_0, T_n and the inventory budget are not defined in "
                        + "that case, so this theorem does not assign them artificial values.")),
                    Paragraph(Text(
                        "This absolute loss bound does not establish that the inventory and "
                        + "collar budget is small enough for the required relative normalizer "
                        + "comparison. Positive selected mass, a favorable signed prime moment, "
                        + "and the full Robin conclusion for every integer greater than 5040 "
                        + "remain separate obligations. The Reg mirror retains the exact "
                        + "source law and bridge as an audit attempt; whole-family variation, "
                        + "sensitivity, actual observational dependence and canonical binding "
                        + "remain unfinished. The rejected-family failure is conditional on the same "
                        + "qualifying source telescope; no qualifying-family inhabitant is supplied. "
                        + "The unfinished audit is tracked at "
                        + "https://github.com/the-omega-institute/trureturing/issues/23015. "
                        + "No completed registration is asserted."))),
                DescribeRole.Theorem))));
}
