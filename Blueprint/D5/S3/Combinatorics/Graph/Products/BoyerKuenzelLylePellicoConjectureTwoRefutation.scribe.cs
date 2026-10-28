using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Products;

internal sealed class BoyerKuenzelLylePellicoConjectureTwoRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Products/" +
        "BoyerKuenzelLylePellicoConjectureTwoRefutation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full finite-graph Conjecture 2 of Boyer--Kuenzel--Lyle--Pellico is false.",
        H("Refuting the unrestricted Conjecture 2"), Blocks(
            Describe.Lean(DescribeId.Create("claim"), DeclarationHandle.Create(Prefix + "claim"),
                H("Conjecture 2 in its complete quantified form"),
                StatementSource.FromAuthor(Disp(C("claim"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The definition retains every finite simple graph and positive integer k. " +
                    "Its left side includes connectedness, the all-j maximal induced proper-coloring " +
                    "well-hued condition, the sequence (alpha,2 alpha,...,k alpha), and chromatic " +
                    "number k. Its right side is a spanning subgraph of a balanced complete k-partite " +
                    "host together with the induced closed-anti-neighborhood exclusion."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("The 3 by 3 rook graph counterexample"),
                StatementSource.FromAuthor(Disp(new Formula.Not(C("claim")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The graph on Fin 3 times Fin 3 joins distinct cells in a common row or column. " +
                    "Its independence number is three and its balanced three-color partition satisfies " +
                    "the right side. The displayed five-cell C4 plus isolated vertex and six-cell C6 are " +
                    "inclusion-maximal induced bipartite sets, of unequal orders five and six. " +
                    "Therefore the graph is not well-hued while the right side holds."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("boyer-kuenzel-lyle-pellico-2025-conjecture-two"),
                    ResolutionKind.Refuted))), []));

    private static Formula C(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
}
