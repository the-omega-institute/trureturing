using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Optimization;

internal sealed class PrepareMeasureLkBoundDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Optimization/PrepareMeasureLkBound";
    private static LibraryNoteRef Source => LibraryNoteRef.Create(
        "D5/L/QuantumContext/divianszkymartonbenevertesi2023certification");

    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula N => F.Id("n");
    private static Formula MDim => F.Id("m");
    private static Formula K => F.Id("k");
    private static Formula M => F.Id("M");
    private static Formula I => F.Id("i");
    private static Formula J => F.Id("j");
    private static Formula Q => F.Id("q");
    private static Formula Assignment => F.Id("f");
    private static Formula Epsilon => Varepsilon;
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) =>
        Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula CastReal(Formula value) => Typed(value, Reals);
    private static Formula Fin(Formula size) => Call("Fin", size);
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);
    private static Formula Matrix(Formula rows, Formula columns) =>
        Call("Matrix", rows, columns, Reals);
    private static Formula MatrixNM => Matrix(Fin(N), Fin(MDim));
    private static Formula SignVectors(Formula size) => Arrow(Fin(size), Fin(D(2)));
    private static Formula Assignments => Arrow(Fin(N), Fin(K));
    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(variable, type), Comma, Sp, body);
    private static Formula Some(Formula variable, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(variable, type), Comma, Sp, body);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Div(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);
    private static Formula Abs(Formula value) => new Formula.Absolute(value);
    private static Formula SumOver(Formula variable, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(variable, Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula MaxOver(Formula variable, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Max, Seq(variable, Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula If(Formula condition, Formula yes, Formula no) =>
        Call("ite", condition, yes, no);
    private static Formula OverDimensions(Formula body) =>
        All(N, Naturals, All(MDim, Naturals, All(M, MatrixNM, body)));
    private static Formula Sign(Formula value) => Call("signValue", value);
    private static Formula Fiber => Call("fiberSum", Assignment, M, J, Q);
    private static Formula FiberMatrix => Parenthesized(Seq(
        Typed(J, Fin(K)), Sp, Typed(Q, Fin(MDim)), Mapsto, Sp, Fiber));
    private static Formula Normalizer =>
        Div(D(1), new Formula.Power(Typed(D(2), Reals), K));
    private static Formula WSet => new Formula.Subscript(
        Seq(Mathcal, Grp(F.Id("W"))), Seq(N, Comma, K));
    private static Formula WDefinition => All(N, Naturals, All(K, Naturals,
        Eq(WSet, Seq(OpenBrace, F.Id("W"), Colon, Sp, Matrix(Fin(N), Fin(K)), Sp, Mid, Sp,
            Some(Assignment, Assignments, All(I, Fin(N), All(J, Fin(K),
                Eq(App(F.Id("W"), I, J), If(Eq(App(Assignment, I), J),
                    Typed(D(1), Reals), Typed(D(0), Reals)))))), CloseBrace))));

    private static Formula SignDefinition => All(F.Id("s"), Fin(D(2)),
        Eq(Sign(F.Id("s")), If(Eq(F.Id("s"), Typed(D(0), Fin(D(2)))),
            new Formula.Negate(Typed(D(1), Reals)), Typed(D(1), Reals))));

    private static Formula ManhattanDefinition => All(Alpha, F.Id("Type"),
        All(Beta, F.Id("Type"), Seq(
            OpenBracket, Call("Fintype", Alpha), CloseBracket, Sp,
            OpenBracket, Call("Fintype", Beta), CloseBracket, Sp,
            All(F.Id("A"), Matrix(Alpha, Beta),
                Eq(Call("manhattan", F.Id("A")),
                    SumOver(I, Alpha, SumOver(J, Beta, Abs(App(F.Id("A"), I, J)))))))));

    private static Formula FiberDefinition => All(N, Naturals, All(MDim, Naturals,
        All(K, Naturals, All(Assignment, Assignments, All(M, MatrixNM,
            All(J, Fin(K), All(Q, Fin(MDim), Eq(Fiber,
                SumOver(I, Fin(N), If(Eq(App(Assignment, I), J),
                    App(M, I, Q), Typed(D(0), Reals)))))))))));

    private static Formula LkDefinition => All(K, Naturals, OverDimensions(
        Eq(Call("Lk", K, M), If(Lt(D(0), K),
            MaxOver(Assignment, Assignments, Call("manhattan", FiberMatrix)),
            Typed(D(0), Reals)))));

    private static Formula LDefinition => OverDimensions(Eq(Call("L", M),
        MaxOver(F.Id("v"), SignVectors(N), SumOver(J, Fin(MDim),
            Abs(SumOver(I, Fin(N), Mul(Sign(App(F.Id("v"), I)), App(M, I, J))))))));

    private static Formula ADefinition => All(K, Naturals, Eq(Call("a", K),
        Mul(Normalizer, SumOver(Epsilon, SignVectors(K),
            Abs(SumOver(I, Fin(K), Sign(App(Epsilon, I))))))));

    private static Formula Claim => All(K, Naturals, Imp(Le(D(3), K),
        Some(F.Id("c"), Reals, And(Lt(F.Id("c"), CastReal(K)),
            OverDimensions(Le(Call("Lk", K, M), Mul(F.Id("c"), Call("L", M))))))));

    private static Formula G(Formula x) => App(new Formula.Subscript(F.Id("g"), K), x);
    private static Formula GDefinition => All(K, Naturals, All(F.Id("x"), Arrow(Fin(K), Reals),
        Eq(G(F.Id("x")), Mul(Normalizer, SumOver(Epsilon, SignVectors(K),
            Abs(SumOver(I, Fin(K), Mul(Sign(App(Epsilon, I)), App(F.Id("x"), I)))))))));
    private static Formula GLowerBound => All(K, Naturals, Imp(Lt(D(0), K),
        All(F.Id("x"), Arrow(Fin(K), Reals),
            Le(Mul(Div(Call("a", K), CastReal(K)),
                SumOver(I, Fin(K), Abs(App(F.Id("x"), I)))), G(F.Id("x"))))));
    private static Formula Comparison => All(K, Naturals, Imp(Lt(D(0), K), OverDimensions(
        All(F.Id("W"), Matrix(Fin(N), Fin(K)), Imp(
            new Formula.Relation(F.Id("W"), FormulaRelationOperator.MemberOf, WSet),
            Le(Mul(Div(Call("a", K), CastReal(K)), Call("manhattan",
                Mul(new Formula.Power(F.Id("W"), Seq(Mathrm, Grp(F.Id("T")))), M))),
                Call("L", M)))))));
    private static Formula C => new Formula.Subscript(F.Id("c"), K);
    private static Formula Constants => All(K, Naturals, Imp(Le(D(3), K), Some(C, Reals,
        And(Eq(C, Div(CastReal(K), Call("a", K))),
            And(Le(Div(Typed(D(3), Reals), Typed(D(2), Reals)), Call("a", K)),
                Lt(C, CastReal(K)))))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Averaging signs improves the prepare-and-measure bound uniformly for every k at least three.",
        H("A strict prepare-and-measure bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sign-value"),
                DeclarationHandle.Create(Module + ".signValue"),
                H("The two real signs"),
                StatementSource.FromAuthor(Disp(SignDefinition)),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The two elements of Fin 2 encode the signs: zero represents minus one, "
                    + "and one represents plus one."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("manhattan"),
                DeclarationHandle.Create(Module + ".manhattan"),
                H("The entrywise Manhattan norm"),
                StatementSource.FromAuthor(Disp(ManhattanDefinition)),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For arbitrary finite row and column types, the Manhattan norm is the "
                    + "sum of the absolute values of all real entries. An empty index type gives zero."))),
                DescribeRole.Definition),
            Describe.Remark(
                DescribeId.Create("standard-basis-rows"),
                H("Matrices with standard basis rows"),
                WDefinition,
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Each function f from Fin n to Fin k encodes exactly one matrix whose "
                    + "ith row is the standard basis vector indexed by f(i). These are precisely "
                    + "the matrices in the source's set.")))),
            Describe.Lean(
                DescribeId.Create("fiber-sum"),
                DeclarationHandle.Create(Module + ".fiberSum"),
                H("Grouped matrix entries"),
                StatementSource.FromAuthor(Disp(FiberDefinition)),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The fiber sum is the (j,q) entry of the transpose product WᵀM: "
                    + "it sums column q over the rows assigned to j."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("lk"),
                DeclarationHandle.Create(Module + ".Lk"),
                H("The k-group matrix functional"),
                StatementSource.FromAuthor(Disp(LkDefinition)),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For positive k, maximize the Manhattan norm of WᵀM over every assignment "
                    + "of rows to k groups. This is the source's L_k. At k equal to zero the "
                    + "definition is extended by zero. The positive branch always has an assignment, "
                    + "even when there are no rows."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("l"),
                DeclarationHandle.Create(Module + ".L"),
                H("The sign-vector matrix functional"),
                StatementSource.FromAuthor(Disp(LDefinition)),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Choose an independent sign for each row, sum the signed rows, and take "
                    + "the vector's Manhattan norm. L is the maximum over all such choices."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a"),
                DeclarationHandle.Create(Module + ".a"),
                H("The averaged absolute sign sum"),
                StatementSource.FromAuthor(Disp(ADefinition)),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The constant a_k averages the absolute sum of k independent uniform signs. "
                    + "The factor two to the power minus k divides by the number of sign vectors."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("Uniform nontightness beyond two groups"),
                StatementSource.FromAuthor(Disp(Eq(Seq(Operatorname, Grp(F.Id("claim"))), Parenthesized(Claim)))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For each k at least three there is one real constant c strictly below k "
                    + "that bounds L_k by c times L for every real matrix and all natural row "
                    + "and column dimensions. This gives a uniform form of the source's conjecture "
                    + "that the factor k in Lemma III.4 is not tight for greater values than two."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("A uniform improvement of the factor k"),
                StatementSource.FromAuthor(Disp(Claim)),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For a real vector x with k coordinates, define the averaged norm:")),
                    new DocumentBlock.DisplayFormula(GDefinition),
                    Paragraph(Text(
                        "Changing coordinate signs leaves this average unchanged. Symmetry of "
                        + "the sign coordinates gives the lower bound for every positive k:")),
                    new DocumentBlock.DisplayFormula(GLowerBound),
                    Paragraph(Text(
                        "For every matrix W with standard basis rows, each sign combination "
                        + "of the rows of WᵀM is a sign combination of the rows of M. Averaging "
                        + "these combinations and summing the column bounds therefore gives:")),
                    new DocumentBlock.DisplayFormula(Comparison),
                    Paragraph(Text(
                        "The average at k equal to three is three halves. Adding a sign cannot "
                        + "decrease the average, by the triangle inequality. Consequently the "
                        + "choice of constant below is strictly smaller than k:")),
                    new DocumentBlock.DisplayFormula(Constants),
                    Paragraph(Text(
                        "Maximizing the comparison over W proves the uniform inequality. "
                        + "The constant depends only on k, so the same bound includes empty "
                        + "matrix dimensions."))),
                DescribeRole.Theorem))));
}
