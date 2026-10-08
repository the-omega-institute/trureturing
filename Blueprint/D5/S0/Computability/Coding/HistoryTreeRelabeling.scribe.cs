using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.Coding;

internal sealed class HistoryTreeRelabelingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "History-dependent relabeling preserves prefix codes and their mass.",
        H("Relabeling a Word Tree"),
        Blocks(
            Paragraph(Text("At each original history h choose a permutation pi(h) of the alphabet. "
                + "Relabel the next letter using that permutation and continue in the original history. "
                + "The inverse decodes a letter before extending the recovered history. These recursions "
                + "are inverse bijections on words. They preserve lengths and the prefix relation in both directions.")),
            Paragraph(Text("Let q(h,a) = p(pi(h)(a)). The conditional mass of a word is the product of "
                + "the rows encountered along its actual path. Its relabeled iid mass is the same product. "
                + "Legal(b,F) uses the canonical prefix-free code condition, excludes the empty word and "
                + "bounds the number of different words at each depth by b.")),
            Describe.Lean(
                DescribeId.Create("history-tree-relabeling"),
                DeclarationHandle.Create("D5/S0/Computability/Coding/HistoryTreeRelabeling.result"),
                H("Transport of codes, budgets and mass"),
                StatementSource.FromAuthor(Disp(F.Seq(
                    Forall, Sp, F.Id("pi,p,q,b,F"), Comma, Sp,
                    F.Id("q(h,a)=p(pi(h)(a))"), Sp, Land, Sp, F.Id("Legal(b,F)"),
                    Sp, Rightarrow, Sp, F.Id("Legal(b,phi(F))"), Sp, Land, Sp,
                    F.Id("T(q,F,N)=T(p,phi(F),N)"), Sp, Land, Sp,
                    F.Id("S(q,F)=S(p,phi(F))")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The level sets are bijective images, so their cardinalities and "
                    + "finite sums are preserved. Reindexing the nonnegative countable sum by the same "
                    + "bijection gives the total-mass identity. No independence or finite-memory condition "
                    + "is imposed on q; the row identity is the required hypothesis."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S0/Computability/Coding/DepthBudgetIidGreedyOptimality"))]));
}
