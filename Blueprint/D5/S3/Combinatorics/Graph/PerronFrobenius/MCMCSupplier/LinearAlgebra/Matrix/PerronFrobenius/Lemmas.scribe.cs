using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PerronFrobenius.MCMCSupplier.LinearAlgebra.Matrix.PerronFrobenius;
internal sealed class LemmasDocument : IScribeDocumentDefinition
{
 public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
 "Finite Perron supplier: Lemmas", H("Finite Perron supplier: Lemmas"), Blocks(
 Paragraph(Text("Apache-2.0 source by Matteo Cipollina, or4nge19/MCMC at b901242fd04b6eff425a177e5c9bc6c56257bc62. The full Apache-2.0 license is reproduced in D5/S3/Combinatorics/Graph/PerronFrobenius/MCMCSupplier/Auxiliary.lean; the canonical supplier family retains the original copyright notices. Unused declarations are omitted and imports are relocated; the retained mathematical proof is reused without a novelty claim.")),
 Paragraph(Text("For a finite irreducible matrix with positive diagonal, shorten a connecting path and pad it with diagonal loops to obtain a common positive power. Positivity of matrix-vector products and the power eigenrelation support the maximizer residual argument. Primitivity is applied to the shifted matrix 1+A inside the supplier; no aperiodicity hypothesis is imposed on the graph-pressure theorem.")))));
}
