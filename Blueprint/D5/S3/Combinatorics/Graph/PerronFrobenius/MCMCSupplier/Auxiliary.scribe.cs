using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PerronFrobenius.MCMCSupplier;
internal sealed class AuxiliaryDocument : IScribeDocumentDefinition
{
 public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
 "Finite Perron supplier: Auxiliary", H("Finite Perron supplier: Auxiliary"), Blocks(
 Paragraph(Text("Apache-2.0 source by Matteo Cipollina, or4nge19/MCMC at b901242fd04b6eff425a177e5c9bc6c56257bc62. The full Apache-2.0 license is reproduced in D5/S3/Combinatorics/Graph/PerronFrobenius/MCMCSupplier/Auxiliary.lean; the canonical supplier family retains the original copyright notices. Unused declarations are omitted and imports are relocated; the retained mathematical proof is reused without a novelty claim.")),
 Paragraph(Text("Finite support minima, normalization of nonnegative nonzero vectors, maximal-coordinate selection, and diagonal matrix comparisons support the Collatz-Wielandt proof. The retained helper statements are used in the positive eigenpair construction or the eigenvalue-modulus bound.")))));
}
