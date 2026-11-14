using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.AlgebraicBoundary;

internal sealed class Source_TauCeti_Topology_Sym_BasicDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pinned real algebraic source: TauCeti.Topology.Sym.Basic.",
        H("Pinned real algebraic source: TauCeti.Topology.Sym.Basic."),
        Blocks(Paragraph(Text("This content adaptation retains selected declarations and proof bodies from TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2, TauCeti/Topology/Sym/Basic.lean. The D5 import paths connect its actual proof dependencies to the original cone boundary consumer. It does not assume a cylindrical decomposition or semialgebraic projection certificate. The original source ownership is retained and no independent escape credit is claimed. Full license and attribution appear in the Lean source and docs/reports/licenses/TauCeti-LICENSE.txt. Each adaptation is retired when the actual pinned mathlib supplies an equivalent statement, replacing consumers by direct applications of that owner.")),
        Paragraph(Text("The finite symmetric power carries the quotient topology of ofFn. A set pulls back to the permutation saturation of tuples, so ofFn is an open quotient map and coordinatewise open conditions descend. Mapping along a continuous/open map is continuous/open by this quotient property. Products of disjoint open coordinate sets give an injective quotient chart, hence the stated open embedding; append uses Fin.append and the product quotient. Compactness and the Hausdorff property descend from the finite permutation quotient under the original CompactSpace/T2Space hypotheses. Properness of ofFn gives closedness with precisely the original topological assumptions. These readouts do not strengthen the weaker normed-field assumptions of the actual coefficient homeomorphism.")))));
}
