using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class CrownOrderPolytopeLogConcavityDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/lundstrom2025crown");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every positive crown has a log-concave full geometric face vector.",
        H("Log-concavity of the full crown f-vector"),
        Blocks(
            Paragraph(Text("Conjecture 3.7 concerns the full geometric face vector, including the empty face and the whole polytope. For natural j with j < 2n+2, write F(n,j) for entry j of crownGeometricFVector n, whose index type is Fin (2*n+2). Thus F(n,0)=1 counts the empty face, and F(n,j) for j>0 counts the actual nonempty exposed faces of affine dimension j-1; entry 2n+1 counts the whole polytope. The published face-count formula is proved from this geometry. The auxiliary Chebyshev factorization and corrected Newton inequalities establish log-concavity.")),
            Describe.Lean(
                DescribeId.Create("crown-geometric-fvector-log-concave"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Geometry/CrownOrderPolytopeLogConcavity.crownGeometricFVector_log_concave"),
                H("Conjecture 3.7 for every positive n"),
                StatementSource.FromAuthor(LogConcavityFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For every positive natural n and every natural k with 0 < k < 2n+1, the product of entries k-1 and k+1 of the actual full geometric f-vector is at most the square of entry k. Thus every internal index is covered, including the comparison with the empty face and the comparison with the whole polytope. The statement is the assertion of source Conjecture 3.7 for the full geometric vector.")),
                    Paragraph(Text("The proof transports the scalar polynomial to the reals and factors T_n-1 separately for even and odd n. Squared Chebyshev U factors retain repeated-root multiplicities; the odd factor U_m+U_(m-1) divides U_(2m). The upstream Newton inequality applied to the negated root multiset, with Vieta's coefficient formula, gives the strong coefficient inequalities. The index is reversed by the polynomial degree, and coefficients beyond that degree vanish. For n at least two the bounds s_0 >= n^2, s_0 <= s_1 <= 2n s_0 repair all three comparisons affected by the constant and linear corrections. The actual n equals one vector is (1,3,3,1). Only the auxiliary scalar polynomial is shown to split over the reals; no real-rootedness of the actual full f-polynomial is asserted."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("crown-order-polytope-log-concavity"),
                    ResolutionKind.Proved))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Geometry/CrownOrderPolytopeChebyshev")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Analytic/RealRootedCoefficientNewton"))
        ]));

    private static Formula LogConcavityFormula()
    {
        var n = Id("n");
        var k = Id("k");
        var naturals = FormulaDsl.Seq(FormulaDsl.Mathbb, FormulaDsl.Grp(FormulaDsl.Id("N")));
        var positiveSize = new Formula.Relation(Num(0), FormulaRelationOperator.LessThan, n);
        var internalIndex = new Formula.RelationChain(
            FormulaRelationOperator.LessThan,
            [Num(0), k, Add(Multiply(Num(2), n), Num(1))]);
        var inequality = new Formula.Relation(
            Multiply(Call("F", n, Subtract(k, Num(1))), Call("F", n, Add(k, Num(1)))),
            FormulaRelationOperator.LessThanOrEqual,
            new Formula.Power(Call("F", n, k), Num(2)));
        return FormulaDsl.Disp(new Formula.Bind(
            FormulaQuantifier.ForAll, FormulaIdentifier.Create("n"), naturals,
            new Formula.Bind(
                FormulaQuantifier.ForAll, FormulaIdentifier.Create("k"), naturals,
                new Formula.Logic(
                    new Formula.Logic(positiveSize, FormulaLogicOperator.And, internalIndex),
                    FormulaLogicOperator.Implies, inequality))));
    }
}
