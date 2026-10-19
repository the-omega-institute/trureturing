using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PerronFrobenius.MCMCSupplier.LinearAlgebra.Matrix.PerronFrobenius;
internal sealed class DominanceDocument : IScribeDocumentDefinition
{
 public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
 "Finite Perron supplier: Dominance", H("Finite Perron supplier: Dominance"), Blocks(
 Paragraph(Text("Apache-2.0 source by Matteo Cipollina, or4nge19/MCMC at b901242fd04b6eff425a177e5c9bc6c56257bc62. The full Apache-2.0 license is reproduced in D5/S3/Combinatorics/Graph/PerronFrobenius/MCMCSupplier/Auxiliary.lean; the canonical supplier family retains the original copyright notices. Unused declarations are omitted and imports are relocated; the retained mathematical proof is reused without a novelty claim.")),
 Paragraph(Text("Take a nonzero complex eigenvector for a spectral value. The triangle inequality gives a real subinvariant vector of coordinate norms, and the Collatz-Wielandt bound controls its eigenvalue modulus. The irreducible positive eigenvector then identifies the actual Perron root. WeightedWalks directly uses this existence result and the spectral bounds for its actual exponential matrix.")))));
}
