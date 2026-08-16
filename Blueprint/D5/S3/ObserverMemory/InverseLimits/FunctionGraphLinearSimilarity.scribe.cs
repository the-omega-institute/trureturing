using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.InverseLimits;

internal sealed class FunctionGraphLinearSimilarityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two eight-state transition matrices are linearly similar over the integers.",
        H("Linear Similarity of the Colliding Function Graphs"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("explicit-integral-transition-matrix-similarity"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/InverseLimits/FunctionGraphLinearSimilarity."
                    + "transition_matrices_linearly_similar"),
                H("An integral unit intertwines the two transition matrices"),
                StatementSource.FromAuthor(SimilarityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a self-map f of Fin 8, transitionMatrix(f) uses the column "
                            + "convention: its (i,j)-entry is one exactly when f(j)=i. The "
                            + "definition imports and applies the frozen tauA and tauB tables; "
                            + "it does not copy either table into a second source.")),
                    Paragraph(Text(
                        "The certificate is the displayed integral matrix similarityWitness. "
                            + "A second explicit integral matrix is checked on both sides as its "
                            + "inverse, so similarityWitness is a unit in the matrix ring. Exact "
                            + "finite arithmetic then verifies transitionMatrix(tauA) P = P "
                            + "transitionMatrix(tauB).")),
                    Paragraph(Text(
                        "This theorem certifies the positive half of proposition 8.5 for the "
                            + "specific pair: the transition matrices lie in the same linear "
                            + "similarity class. The frozen collision theorem separately certifies "
                            + "that no permutation conjugates the underlying based function graphs.")),
                    Paragraph(Text(
                        "Repository, pinned-Mathlib, and GitHub Lean-code searches found no equal "
                            + "or stronger declaration. The proof therefore uses the explicit "
                            + "finite certificate and Mathlib's standard matrix-unit interface."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula SimilarityFormula()
    {
        Formula p = F.Id("P");
        Formula a = F.Id("tauA");
        Formula b = F.Id("tauB");
        Formula finEight = Apply(F.Id("Fin"), D(8));
        Formula matrix = Apply(
            Seq(Operatorname, Grp(F.Id("Matrix"))),
            finEight,
            finEight,
            Seq(Mathbb, Grp(F.Id("Z"))));
        Formula transitionA = Apply(F.Id("transitionMatrix"), a);
        Formula transitionB = Apply(F.Id("transitionMatrix"), b);

        return Disp(Seq(
            Exists, Sp, p, Colon, Sp, matrix, Comma, Esc,
            Apply(Seq(Operatorname, Grp(F.Id("IsUnit"))), p), Sp, Land, Sp,
            transitionA, Sp, Star, Sp, p, Sp, Eq, Sp,
            p, Sp, Star, Sp, transitionB, Dot));
    }
}
