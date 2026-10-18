using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PerronFrobenius.MCMCSupplier.LinearAlgebra.Matrix.PerronFrobenius;
internal sealed class CollatzWielandtDocument : IScribeDocumentDefinition
{
 public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
 "Finite Perron supplier: CollatzWielandt", H("Finite Perron supplier: CollatzWielandt"), Blocks(
 Paragraph(Text("Apache-2.0 source by Matteo Cipollina, or4nge19/MCMC at b901242fd04b6eff425a177e5c9bc6c56257bc62. The full Apache-2.0 license is reproduced in D5/S3/Combinatorics/Graph/PerronFrobenius/MCMCSupplier/Auxiliary.lean; the canonical supplier family retains the original copyright notices. Unused declarations are omitted and imports are relocated; the retained mathematical proof is reused without a novelty claim.")),
 Paragraph(Text("The infimum of supported coordinate ratios is upper semicontinuous on the finite simplex. Compactness supplies a maximizer. A maximal-coordinate bound makes its supremum finite; positive diagonal similarity compares arbitrary subinvariant vectors with a positive eigenvector. These statements feed the actual positive Perron construction and the complex eigenvalue-modulus bound.")))));
}
