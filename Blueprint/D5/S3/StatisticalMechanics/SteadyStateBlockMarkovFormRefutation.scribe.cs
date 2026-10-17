using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics;

internal sealed class SteadyStateBlockMarkovFormRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/StatisticalMechanics/SteadyStateBlockMarkovFormRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/saribeiroprosenbernard2024symmetryclasses");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An irreducible steady-state block of a four-state Markov generator is not similar to any real Markov generator, even by a complex change of basis.",
        H("A steady-state symmetry block without Markov form"), Blocks(
            Paragraph(Text(
                "Vectors are columns, Fin n indexes all n coordinates, and all finite sums include every index. "
                    + "Matrix.mulVec denotes matrix action on a column vector. The superscript T denotes transpose; "
                    + "matrix products and scalar multiples use the usual multiplication notation. "
                    + "The expression M.map(Complex.ofReal) embeds each real entry of M into the complex numbers. "
                    + "The symbol 1 denotes the identity matrix of the indicated size.")),
            Describe.Lean(
                DescribeId.Create("steady-state-block-markov-generator"),
                DeclarationHandle.Create(Prefix + "IsMarkovGenerator"),
                H("Real Markov generators"),
                StatementSource.FromAuthor(Disp(GeneratorFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Equations (2)-(4) require real entries, nonnegative off-diagonal entries and zero column sums. "
                        + "The real matrix type expresses Eq. (2); the two clauses express Eqs. (3) and (4). "
                        + "No sign condition is imposed separately on the diagonal."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("steady-state-block-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The steady-state block conjecture"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "After Eq. (5), the conjecture asks whether the irreducible block containing an invariant "
                            + "probability can be recast into Markov form. Here L is a real Markov generator, "
                            + "U is a real orthogonal matrix commuting with L, and p is stationary. "
                            + "The probability condition is written in full: every coordinate is nonnegative "
                            + "and their sum is one.")),
                    Paragraph(Text(
                        "The columns of V are orthonormal and span an L-invariant subspace. They lie in the "
                            + "u-eigenspace of U, and the quantified condition on x says they span that whole "
                            + "eigenspace. The subspace contains p. Its restriction is V^T L V. "
                            + "Irreducibility means that every complex unitary matrix commuting with this restriction "
                            + "is a complex scalar multiple of the identity. Orthogonal and unitary group membership "
                            + "mean U^T U = U U^T = 1 and X* X = X X* = 1, respectively, where X* is conjugate transpose.")),
                    Paragraph(Text(
                        "The conclusion allows any invertible complex S: IsUnit S is invertibility in the "
                            + "complex matrix algebra. Its conjugate of the restriction must equal a real Markov "
                            + "generator B embedded into the complex matrices. The dimensions N and d range over "
                            + "all natural numbers, with no separate positivity assumption. "
                            + "Appendix A proves a sufficient case under the additional assumption (A3) that the "
                            + "conditional probabilities are zero or one; that assumption is absent from this conjecture."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("steady-state-block-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A four-state counterexample"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Named("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Take N = 4 and let L be 1/256 times the matrix with rows "
                            + "(-295, 25, 25, 281), (273, -303, 17, 17), (7, 263, -313, 7) and "
                            + "(15, 15, 271, -305). Every off-diagonal entry is positive and every column sums "
                            + "to zero. The stationary probability is p = (1/64)(17, 17, 15, 15). "
                            + "For the column vector v = (1, -1, 1, -1), set U = 1 - v v^T/2. "
                            + "This orthogonal involution commutes with L.")),
                    Paragraph(Text(
                        "Let V be 1/2 times the four-by-three matrix with rows (1, 1, -1), (1, 1, 1), "
                            + "(1, -1, 1) and (1, -1, -1). Its columns are orthonormal and span the entire "
                            + "+1 eigenspace of U. This subspace contains p = V(1/2, 1/32, 0) and is "
                            + "L-invariant. Its restriction A = V^T L V has rows "
                            + "(0, 0, 0), (5/64, -5/4, -1) and (-1/16, 1, -5/4).")),
                    Paragraph(Text(
                        "To see irreducibility, view A over the complex numbers. A unitary X commuting with A "
                            + "also commutes with its conjugate transpose A^T. The kernel of A^T is spanned by "
                            + "e_0 = (1, 0, 0), so X e_0 is a scalar multiple of e_0. The three columns "
                            + "e_0, A e_0 = (0, 5/64, -1/16) and A^2 e_0 = (0, -9/256, 5/32) have "
                            + "determinant 41/4096 and hence form a basis. Commutation with A forces X to be "
                            + "the same scalar on all three basis vectors.")),
                    Paragraph(Text(
                        "Every real three-by-three matrix B with nonnegative off-diagonal entries satisfies "
                            + "3 tr(B^2) - (tr B)^2 = (B_00 - B_11)^2 + (B_11 - B_22)^2 + "
                            + "(B_22 - B_00)^2 + 6(B_01 B_10 + B_02 B_20 + B_12 B_21) >= 0. "
                            + "For A, tr A = -5/2 and tr(A^2) = 9/8, giving "
                            + "3 tr(A^2) - (tr A)^2 = -23/8. Both traces are invariant under complex similarity. "
                            + "Consequently no invertible complex S can make S^(-1) A S a real Markov generator."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("sa-ribeiro-prosen-bernard-2024-steady-state-block-refutation"),
                    ResolutionKind.Refuted))
        )));

    private static Formula GeneratorFormula() => All("n", Naturals(),
        All("M", Matrices(V("n"), V("n"), Reals()),
            IffOf(Call("IsMarkovGenerator", V("M")),
                And(All("i", Fin(V("n")), All("j", Fin(V("n")),
                        Imp(NotEqual(V("i"), V("j")), LE(D(0), At(V("M"), V("i"), V("j")))))),
                    All("j", Fin(V("n")),
                        Equal(SumOver("i", Fin(V("n")), At(V("M"), V("i"), V("j"))), D(0)))))));

    private static Formula ClaimFormula()
    {
        Formula block = Multiply(Multiply(Transpose(V("V")), V("L")), V("V"));
        Formula complexBlock = Complexify(block);
        Formula realStates = States(V("N"));
        Formula coordinates = States(V("d"));
        Formula complexMatrices = Matrices(V("d"), V("d"), Complexes());
        Formula realMatrices = Matrices(V("d"), V("d"), Reals());
        Formula probability = And(All("i", Fin(V("N")), LE(D(0), At(V("p"), V("i")))),
            Equal(SumOver("i", Fin(V("N")), At(V("p"), V("i"))), D(1)));
        Formula entireEigenspace = All("x", realStates,
            Imp(Equal(MulVec(V("U"), V("x")), Multiply(V("u"), V("x"))),
                Some("c", coordinates, Equal(MulVec(V("V"), V("c")), V("x")))));
        Formula irreducibility = All("X", complexMatrices,
            Imp(Member(V("X"), At(Qualified("Matrix", "unitaryGroup"), Fin(V("d")), Complexes())),
                Imp(Equal(Multiply(V("X"), complexBlock), Multiply(complexBlock, V("X"))),
                    Some("mu", Complexes(), Equal(V("X"),
                        Multiply(V("mu"), Typed(D(1), complexMatrices)))))));
        Formula conclusion = Some("S", complexMatrices, Some("B", realMatrices,
            And(Call("IsUnit", V("S")), And(Call("IsMarkovGenerator", V("B")),
                Equal(Multiply(Multiply(Inverse(V("S")), complexBlock), V("S")),
                    Complexify(V("B")))))));
        Formula[] blockHypotheses =
        [
            Equal(Multiply(Transpose(V("V")), V("V")), D(1)),
            Equal(Multiply(V("L"), V("V")), Multiply(V("V"), block)),
            Equal(Multiply(V("U"), V("V")), Multiply(V("u"), V("V"))),
            entireEigenspace,
            Some("c", coordinates, Equal(MulVec(V("V"), V("c")), V("p"))),
            irreducibility
        ];
        Formula body = Implications(blockHypotheses, conclusion);
        body = All("d", Naturals(), All("V", Matrices(V("N"), V("d"), Reals()),
            All("u", Reals(), body)));
        Formula[] hypotheses =
        [
            Call("IsMarkovGenerator", V("L")),
            Member(V("U"), At(Qualified("Matrix", "orthogonalGroup"), Fin(V("N")), Reals())),
            Equal(Multiply(V("U"), V("L")), Multiply(V("L"), V("U"))),
            probability,
            Equal(MulVec(V("L"), V("p")), D(0))
        ];
        body = Implications(hypotheses, body);
        return IffOf(Named("claim"), All("N", Naturals(),
            All("L", Matrices(V("N"), V("N"), Reals()),
                All("U", Matrices(V("N"), V("N"), Reals()), All("p", realStates, body)))));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(V(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => At(Named(name), arguments);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(V("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(V("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(V("C")));
    private static Formula Fin(Formula size) => Call("Fin", size);
    private static Formula States(Formula size) => Parenthesized(new Formula.TypeArrow(Fin(size), Reals()));
    private static Formula Matrices(Formula rows, Formula columns, Formula field) =>
        Call("Matrix", Fin(rows), Fin(columns), field);
    private static Formula Transpose(Formula matrix) => new Formula.Power(Parenthesized(matrix), V("T"));
    private static Formula Inverse(Formula matrix) =>
        new Formula.Power(Parenthesized(matrix), new Formula.Negate(D(1)));
    private static Formula Complexify(Formula matrix) =>
        At(Seq(Parenthesized(matrix), Dot, Named("map")), Qualified("Complex", "ofReal"));
    private static Formula MulVec(Formula matrix, Formula vector) =>
        At(Qualified("Matrix", "mulVec"), matrix, vector);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Typed(V(name), type)), Sp, Parenthesized(body));
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula LE(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Member(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula IffOf(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Implications(Formula[] hypotheses, Formula conclusion)
    {
        for (var index = hypotheses.Length - 1; index >= 0; index--)
            conclusion = Imp(hypotheses[index], conclusion);
        return conclusion;
    }
}
