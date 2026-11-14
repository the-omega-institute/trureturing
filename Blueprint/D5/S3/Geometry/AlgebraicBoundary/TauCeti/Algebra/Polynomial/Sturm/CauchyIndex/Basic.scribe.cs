using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.AlgebraicBoundary;

internal sealed class Source_TauCeti_Algebra_Polynomial_Sturm_CauchyIndex_BasicDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pinned real algebraic source: TauCeti.Algebra.Polynomial.Sturm.CauchyIndex.Basic.",
        H("Pinned real algebraic source: TauCeti.Algebra.Polynomial.Sturm.CauchyIndex.Basic."),
        Blocks(Paragraph(Text("This content adaptation retains selected declarations and proof bodies from TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2, TauCeti/Algebra/Polynomial/Sturm/CauchyIndex/Basic.lean. The D5 import paths connect its actual proof dependencies to the original cone boundary consumer. It does not assume a cylindrical decomposition or semialgebraic projection certificate. The original source ownership is retained and no independent escape credit is claimed. Full license and attribution appear in the Lean source and docs/reports/licenses/TauCeti-LICENSE.txt. Each adaptation is retired when the actual pinned mathlib supplies an equivalent statement, replacing consumers by direct applications of that owner.")),
        Paragraph(Text("The Cauchy jump is determined by the two one-sided signs of the rational quotient, and cauchyIndex is the finite sum of these jumps over the chosen pole set. Empty and singleton sets reduce to the empty and singleton sums. A disjoint union is Finset.sum_union; splitting an open interval at a point includes precisely the separate jump at that point. Adding a polynomial multiple of the denominator leaves the quotient jump unchanged at a pole, and common right multiplication cancels wherever the original nonvanishing condition holds. Pinned evaluation, one-sided sign and finite-sum laws supply these identities. The retained recurrence, not an interval readout wrapper, supplies the Euclidean root-count path.")))));
}
