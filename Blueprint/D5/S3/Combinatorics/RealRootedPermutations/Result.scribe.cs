using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.RealRootedPermutations;

internal sealed class ResultDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exactly the unimodal permutations occur as coefficient orders of products of positive linear factors.",
        H("All unimodal coefficient orders arise"), Blocks(
            Describe.Lean(DescribeId.Create("real-rooted-permutation-result"),
                DeclarationHandle.Create("D5/S3/Combinatorics/RealRootedPermutations/Result.result"),
                H("Answer to Question 4.6"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/PermutationPatterns/ball2022independent")),
                Blocks(
                    Paragraph(Text("For every natural n and permutation of Fin(n+1), there are n+1 strictly positive real parameters whose nonconstant product coefficients weakly increase in that permutation order if and only if the permutation is unimodal. Value v denotes coefficient index v+1, so the constant coefficient is omitted. The definitions follow equations (1) and (4) of the cited article, and the conclusion answers Question 4.6 in Section 4 for polynomials of full degree.")),
                    Paragraph(Text("LogConcave.unimodal_of_arises gives the necessary condition, including weak orders with a tie at the coefficient maximum. Realization.realize_strict gives the sufficient condition with strictly increasing coefficients, hence also a weak order. The realization uses integer exponent heights and a base larger than the number of subset terms. The classification of unweighted graph matching permutations is a separate question."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("ball-galvin-hyry-weingartner-2022-unimodal-coefficient-permutations"),
                    ResolutionKind.Proved)))));
}
