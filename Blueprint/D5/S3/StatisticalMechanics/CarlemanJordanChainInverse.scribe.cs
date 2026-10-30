using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics;

internal sealed class CarlemanJordanChainInverseDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/StatisticalMechanics/CarlemanJordanChainInverse";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Eigenstructure/grosjeanhuillet2016carleman");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The inverse of each normalized critical Carleman Jordan chain is an increasing-path sum.",
        H("Critical Carleman matrices and normalized Jordan chains"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("carleman"),
                DeclarationHandle.Create(Module + ".carleman"),
                H("A principal Carleman truncation"),
                StatementSource.FromAuthor(Disp(CarlemanFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The coefficient sequence α determines the formal power series φ = PowerSeries.mk α. "
                    + "The entry in row i and column j is the coefficient of degree j.val + 1 in φ raised to i.val + 1. "
                    + "Thus Fin n indexes the first n positive powers and positive coefficient degrees, with an index shift of one. "
                    + "This is the principal truncation of the Carleman matrix in equation (2) of Grosjean and Huillet "
                    + "(snlmatrixRR.tex, lines 126–141). The definition accepts any real coefficient sequence; "
                    + "the critical-case assumptions enter the inverse theorem."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("is-jordan-chain"),
                DeclarationHandle.Create(Module + ".IsJordanChain"),
                H("A normalized upper triangular Jordan chain"),
                StatementSource.FromAuthor(Disp(JordanChainFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Subtract the identity matrix from the Carleman truncation. A column of w whose index value is zero is annihilated by this difference, "
                    + "and every later column maps to the preceding column. The row at index zero has entry one in column zero and zero elsewhere, "
                    + "and entries below the diagonal vanish. For n > 0 these conditions make column zero the zeroth coordinate vector; "
                    + "for n = 0 all three conditions are vacuous. "
                    + "They express the normalization in the critical-case Jordanization "
                    + "(snlmatrixRR.tex, lines 403–428 and 439–440). "
                    + "In the nonzero branch, ⟨j.val − 1⟩ denotes the element of Fin n with natural value j.val − 1; "
                    + "the branch condition and j.val < n give its bound."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("sigma"),
                DeclarationHandle.Create(Module + ".sigma"),
                H("The increasing-path weights"),
                StatementSource.FromAuthor(Disp(SigmaFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For zero edges the weight is one at index zero and zero elsewhere. "
                    + "To obtain the weight of paths with m + 1 edges ending at j, sum over i < j the weight of an m-edge path "
                    + "ending at i multiplied by the Carleman entry from i to j. Every path is strictly increasing and starts at zero. "
                    + "Appending its final edge gives exactly the source's path sum, with sigma α n m j corresponding to σ(m,j.val + 1) "
                    + "(snlmatrixRR.tex, lines 442–449). This recurrence also covers an empty index type."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("Existence and the critical-case inverse formula"),
                StatementSource.FromAuthor(Disp(IffOf(Local("claim"), ClaimBody()))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every real coefficient sequence with α 0 = 0, α 1 = 1 and α 2 nonzero, "
                    + "each positive-size principal truncation has a normalized upper triangular Jordan chain. "
                    + "Every matrix w satisfying those conditions has nonzero determinant, and its inverse at k ≤ j equals sigma α n k.val j. "
                    + "The source's conjecture W⁻¹(k,k′) = σ(k − 1,k′), for k′ ≥ k ≥ 1, "
                    + "becomes this identity after shifting both matrix indices by one "
                    + "(snlmatrixRR.tex, lines 449–452). The statement concerns finite principal truncations and formal coefficients, "
                    + "for which analytic convergence is unnecessary."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("Jordan-chain inversion by powers and paths"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Fix α with α 0 = 0, α 1 = 1 and α 2 ≠ 0, and fix n > 0. "
                        + "Write P = carleman α n and A = P − I. Put f = PowerSeries.mk (fun k => α (k + 1)); "
                        + "then φ = Xf and the constant coefficient of f is one. "
                        + "Extracting coefficients of X raised to i.val + 1 times f raised to i.val + 1 shows that A(i,j) = 0 for j ≤ i. "
                        + "When j.val = i.val + 1, the coefficient of degree one in that power of f gives "
                        + "A(i,j) = (↑(i.val + 1) : ℝ) α 2. This entry is nonzero, because i.val + 1 is a positive natural number and α 2 ≠ 0.")),
                    Paragraph(Text(
                        "The columns are constructed by a finite substitution argument. "
                        + "For k < n and a vector b vanishing at every index with value at least k, "
                        + "construct v with Av = b, with v zero at index zero and above index k. "
                        + "At k = 0 take v = 0. In the step from k to k + 1, let r and p have values k and k + 1, "
                        + "put c = b(r)/A(r,p), and let e be supported only at p with value c. "
                        + "The vector b − Ae vanishes at every index with value at least k: the row r cancels by the choice of c, "
                        + "and the later rows vanish by the support of b and strict upper triangularity of A. "
                        + "The induction hypothesis gives u with Au = b − Ae, and v = u + e has the required support and image.")),
                    Paragraph(Text(
                        "Now construct the columns in order. The zeroth column is the zeroth coordinate vector, which A annihilates. "
                        + "For a later column with index value t, the preceding column vanishes at index values at least t. "
                        + "Apply the substitution argument with k = t to obtain a new column with zero first coordinate, "
                        + "support through t and image equal to the preceding column. Replace only column t, preserving the earlier columns. "
                        + "After n steps the resulting matrix satisfies IsJordanChain α n w.")),
                    Paragraph(Text(
                        "For any such w, induction on m gives A raised to m times column j equal to column j.val − m "
                        + "when m ≤ j.val, and equal to zero otherwise. The initial case uses the identity matrix; "
                        + "the induction step applies the chain equation, with the zeroth column terminating the chain. "
                        + "Define q(k,j) = (A raised to k.val)(0,j), using the zeroth finite index, which exists because n > 0. "
                        + "The entry (q w)(k,j) is the zeroth coordinate of A raised to k.val times column j. "
                        + "The first-row normalization makes this entry one exactly when k = j and zero otherwise. "
                        + "Hence q w = I. For finite square matrices this left inverse gives a nonzero determinant and w⁻¹ = q.")),
                    Paragraph(Text(
                        "Finally, induction on m identifies (A raised to m)(0,j) with sigma α n m j. "
                        + "For m = 0 the first row of the identity matrix is the zero-edge path weight. "
                        + "For m + 1, matrix multiplication sums (A raised to m)(0,i) A(i,j) over i. "
                        + "If i < j, the off-diagonal entry A(i,j) equals P(i,j), and the induction hypothesis gives the shorter-path weight. "
                        + "If i ≥ j, strict upper triangularity makes the summand zero. "
                        + "The resulting sum is precisely the recurrence defining sigma. "
                        + "Substitution into w⁻¹ = q proves the claimed inverse entries for k ≤ j."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("grosjean-huillet-2016-carleman-jordan-chain-inverse"),
                    ResolutionKind.Proved)))));

    private static Formula CarlemanFormula()
    {
        Formula series = At(Qualified("PowerSeries", "mk"), Alpha);
        Formula coefficient = At(Qualified("PowerSeries", "coeff"),
            Add(Val("j"), D(1)), Pow(series, Add(Val("i"), D(1))));
        return Parameters(All("i", FinN(), All("j", FinN(),
            Equal(LocalCall("carleman", Alpha, V("n"), V("i"), V("j")), coefficient))));
    }

    private static Formula JordanChainFormula()
    {
        Formula difference = Sub(LocalCall("carleman", Alpha, V("n")), Typed(D(1), MatrixN()));
        Formula column = LambdaOf("i", FinN(), At(V("w"), V("i"), V("j")));
        Formula precedingColumn = LambdaOf("i", FinN(), At(V("w"), V("i"),
            FiniteIndex(Sub(Val("j"), D(1)))));
        Formula chain = All("j", FinN(), Equal(
            At(Qualified("Matrix", "mulVec"), difference, column),
            If(Equal(Val("j"), D(0)), Typed(D(0), VectorN()), precedingColumn)));
        Formula firstRow = All("i", FinN(), All("j", FinN(),
            Arrow(Equal(Val("i"), D(0)), Equal(At(V("w"), V("i"), V("j")),
                If(Equal(Val("j"), D(0)), Typed(D(1), Reals()), Typed(D(0), Reals()))))));
        Formula triangular = All("i", FinN(), All("j", FinN(), Arrow(Lt(V("j"), V("i")),
            Equal(At(V("w"), V("i"), V("j")), Typed(D(0), Reals())))));
        return Parameters(All("w", MatrixN(), IffOf(LocalCall("IsJordanChain", Alpha, V("n"), V("w")),
            And(chain, And(firstRow, triangular)))));
    }

    private static Formula SigmaFormula()
    {
        Formula initial = All("j", FinN(), Equal(LocalCall("sigma", Alpha, V("n"), D(0), V("j")),
            If(Equal(Val("j"), D(0)), Typed(D(1), Reals()), Typed(D(0), Reals()))));
        Formula summand = If(Lt(V("i"), V("j")),
            Mul(LocalCall("sigma", Alpha, V("n"), V("m"), V("i")),
                LocalCall("carleman", Alpha, V("n"), V("i"), V("j"))), Typed(D(0), Reals()));
        Formula successor = All("m", Naturals(), All("j", FinN(), Equal(
            LocalCall("sigma", Alpha, V("n"), Add(V("m"), D(1)), V("j")), SumOver("i", FinN(), summand))));
        return Parameters(And(initial, successor));
    }

    private static Formula ClaimBody()
    {
        Formula chain = LocalCall("IsJordanChain", Alpha, V("n"), V("w"));
        Formula inverseEntries = All("k", FinN(), All("j", FinN(), Arrow(Le(V("k"), V("j")),
            Equal(At(At(Qualified("Inv", "inv"), V("w")), V("k"), V("j")),
                LocalCall("sigma", Alpha, V("n"), Val("k"), V("j"))))));
        Formula inverses = All("w", MatrixN(), Arrow(chain,
            And(At(Qualified("IsUnit"), At(Qualified("Matrix", "det"), V("w"))), inverseEntries)));
        return All("α", Coefficients(), Arrow(Equal(At(Alpha, D(0)), Typed(D(0), Reals())),
            Arrow(Equal(At(Alpha, D(1)), Typed(D(1), Reals())),
                Arrow(NotEqual(At(Alpha, D(2)), Typed(D(0), Reals())), All("n", Naturals(),
                    Arrow(Lt(D(0), V("n")), And(Some("w", MatrixN(), chain), inverses)))))));
    }

    private static Formula Parameters(Formula body) => All("α", Coefficients(), All("n", Naturals(), body));
    private static Formula Coefficients() => Arrow(Naturals(), Reals());
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula FinN() => At(Qualified("Fin"), V("n"));
    private static Formula MatrixN() => At(Qualified("Matrix"), FinN(), FinN(), Reals());
    private static Formula VectorN() => Arrow(FinN(), Reals());
    private static Formula Val(string name) => At(Qualified("Fin", "val"), V(name));
    private static Formula FiniteIndex(Formula value) => Typed(Seq(Langle, value, Rangle), FinN());
    private static Formula Local(string name) =>
        Qualified("D5", "S3", "StatisticalMechanics", "CarlemanJordanChainInverse", name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula V(string name) => name == "α" ? Alpha : F.Id(name);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(V(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Arrow(Formula premise, Formula conclusion) =>
        new Formula.TypeArrow(Parenthesized(premise), Parenthesized(conclusion));
    private static Formula If(Formula condition, Formula yes, Formula no) =>
        At(Qualified("ite"), condition, yes, no);
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(V(name), Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula IffOf(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Pow(Formula value, Formula exponent) => new Formula.Power(Parenthesized(value), exponent);
}
