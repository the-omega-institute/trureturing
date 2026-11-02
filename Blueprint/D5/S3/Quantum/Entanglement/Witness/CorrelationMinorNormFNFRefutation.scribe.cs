using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.Witness;

internal sealed class CorrelationMinorNormFNFRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Entropy/peledteenicarmicohen2021minor");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A separable qubit-ququart state violates the conjectured correlation-minor operator-norm bound without filter normal form.",
        H("A correlation-minor bound fails without filter normal form"),
        Blocks(
            Definition("hermitian-basis", "IsHermBasis", "Orthonormal Hermitian bases", HermBasisFormula(),
                "A family a consists of Hermitian n by n complex matrices, has exactly n squared members, "
                    + "and has trace-product pairing one on equal indices and zero on unequal indices. "
                    + "This is the Hilbert–Schmidt normalization at TeX line 177, without a factor of two. "
                    + "The definition itself permits zero dimensions."),
            Definition("correlation", "corr", "The real correlation matrix", CorrelationFormula(),
                "For a complex matrix ρ on the product of the two local index spaces and local matrix families a and b, "
                    + "the correlation entry is the real part of the trace of ρ times the Kronecker product of a i and b j. "
                    + "For a density matrix and Hermitian local observables, this is the source's correlation matrix "
                    + "at TeX lines 179–183. The formula defines real entries for arbitrary input matrices and families as well."),
            Definition("compound", "compound", "The matrix of ordered minors", CompoundFormula(),
                "Rows and columns are indexed by finite subsets of cardinality h. "
                    + "Each entry is the determinant of the submatrix whose rows and columns are enumerated increasingly "
                    + "by Finset.orderEmbOfFin. This specifies the signs of the minors. "
                    + "It is the compound matrix described at TeX lines 214–225, extended to every natural h."),
            Definition("cmn-infinity", "cmnInf", "The correlation-minor operator norm", CmnInfFormula(),
                "The quantity cmnInf is the Euclidean operator norm of the h-th compound matrix. "
                    + "It is the Schatten infinity norm in the correlation-minor construction at TeX lines 225–233 "
                    + "and in Theorem 3 at lines 274–280. The norm acts between the Euclidean spaces indexed by the column and row subsets."),
            Definition("bound", "bound", "The proposed separability bound", BoundFormula(),
                "The larger and smaller local dimensions determine the right hand side of Theorem 3 at TeX lines 275–280. "
                    + "The dimensions are included in the real numbers, and the exponent is real: subtract one from the real value of h, "
                    + "then divide by two. In particular, the subtraction is not truncated natural subtraction. "
                    + "The expression is defined for all natural arguments, using real division and real powers."),
            Definition("claim", "claim", "The conjecture without filter normal form", ClaimFormula(),
                "The conjecture at TeX line 281 removes filter normal form from Theorem 3. "
                    + "Here both local dimensions are at least two, the natural order h satisfies the product-dimension lower bound "
                    + "on h squared and the smaller-dimension-squared upper bound, and ρ is any separable state. "
                    + "Separability means a finite convex combination of tensor products of positive semidefinite trace-one local matrices. "
                    + "For every pair of normalized Hermitian bases the correlation-minor operator norm is asserted to obey the bound. "
                    + "There is no condition of filter normal form."),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A separable qubit-ququart counterexample"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(ClaimProposition())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Take local dimensions two and four and order three. Let Eⱼⱼ be the four-dimensional diagonal matrix units. "
                            + "On the two-dimensional factor set P₀ = [[1,0],[0,0]], "
                            + "P₁ = [[1,2],[2,4]]/5 and P₂ = [[1,−2],[−2,4]]/5. "
                            + "Use the state ρ = (333/1000) ∑ⱼ₌₀² Pⱼ ⊗ Eⱼⱼ + I₈/8000. "
                            + "Each Pⱼ is positive semidefinite because it is a positive multiple of a vector outer product, "
                            + "and each has trace one. The Eⱼⱼ are also positive semidefinite with trace one. "
                            + "The maximally mixed local matrices I₂/2 and I₄/4 have the same properties. "
                            + "Thus ρ is a convex combination of four product density matrices, with weights "
                            + "333/1000, 333/1000, 333/1000 and 1/1000.")),
                    Paragraph(Text(
                        "Choose the first local basis as (I,Z,X,Y)/√2. Choose the second as the four diagonal matrix units, "
                            + "followed by (Eₐᵦ + Eᵦₐ)/√2 and (−iEₐᵦ + iEᵦₐ)/√2 for the six pairs a < b, "
                            + "in the order (0,1), (0,2), (0,3), (1,2), (1,3), (2,3). "
                            + "Conjugate transposition verifies that every basis matrix is Hermitian; "
                            + "the trace products give the identity pairing. Both families have the required squared dimensions.")),
                    Paragraph(Text(
                        "Computing the correlation matrix one row at a time gives a four by sixteen matrix. "
                            + "Its first four columns are 1/√2 times the matrix with rows "
                            + "(1333/4000,1333/4000,1333/4000,1/4000), "
                            + "(333/1000,−999/5000,−999/5000,0), "
                            + "(0,333/1250,−333/1250,0) and (0,0,0,0); its remaining columns vanish. "
                            + "Select the compound row indexed by {0,1,2} and the four distinct compound columns indexed by "
                            + "{0,1,2}, {0,1,3}, {0,2,3} and {1,2,3}. "
                            + "In increasing index order their determinants are, respectively, "
                            + "147815037/1562500000, 110889/5000000000, −110889/5000000000 and 332667/12500000000, "
                            + "each divided by (√2)³. Their squares sum to 559341805929555807/500000000000000000000.")),
                    Paragraph(Text(
                        "For any real matrix, apply its conjugate transpose to the unit coordinate vector at a selected row. "
                            + "The squared Euclidean norm of the resulting vector is the sum of the squared entries in that row. "
                            + "The operator-norm inequality and invariance under conjugate transposition bound this sum by the squared operator norm. "
                            + "Restricting the sum to any injectively selected columns only decreases it. "
                            + "Applied to the four minors above, this gives a lower bound of "
                            + "559341805929555807/500000000000000000000 for the squared correlation-minor norm.")),
                    Paragraph(Text(
                        "At dimensions two and four and order three, the proposed bound is 3/(64√2). "
                            + "Its square is 9/8192, strictly below the lower bound just obtained. "
                            + "If the asserted universal inequality held, its instance at this separable state and these two bases "
                            + "would bound the correlation-minor norm by 3/(64√2): the dimension conditions hold because 8 ≤ 9 and 3 ≤ 4. "
                            + "Both sides are nonnegative, so squaring would contradict the strict numerical gap. "
                            + "Therefore the bound does not hold for all separable states without filter normal form."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("peled-teeni-carmi-cohen-2021-correlation-minor-norm-fnf"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Definition(string id, string declaration, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula HermBasisFormula()
    {
        Formula pairing = All("i", FinOf(V("m")), All("j", FinOf(V("m")),
            Equal(Trace(Multiply(At(V("a"), V("i")), At(V("a"), V("j")))),
                At(Qualified("ite"), Equal(V("i"), V("j")), Typed(D(1), Complexes), Typed(D(0), Complexes)))));
        Formula body = And(All("i", FinOf(V("m")),
            At(Qualified("Matrix", "IsHermitian"), At(V("a"), V("i")))),
            And(Equal(V("m"), Power(V("n"), D(2))), pairing));
        return All("n", Naturals, All("m", Naturals, All("a", HermFamily(V("n"), V("m")),
            Iff(LocalCall("IsHermBasis", V("a")), body))));
    }

    private static Formula CorrelationFormula()
    {
        Formula scalarProduct = LambdaOf("x1", Complexes,
            LambdaOf("x2", Complexes, Multiply(V("x1"), V("x2"))));
        Formula entry = At(Qualified("Complex", "re"), Trace(Multiply(Rho,
            At(Qualified("Matrix", "kroneckerMap"), scalarProduct, At(V("a"), V("i")), At(V("b"), V("j"))))));
        Formula body = Equal(Typed(LocalCall("corr", Rho, V("a"), V("b")),
            Matrix(FinOf(V("ma")), FinOf(V("mb")), Reals)),
            LambdaOf("i", FinOf(V("ma")), LambdaOf("j", FinOf(V("mb")), entry)));
        return All("da", Naturals, All("db", Naturals, All("ma", Naturals, All("mb", Naturals,
            All("ρ", BipartiteMatrix(), All("a", HermFamily(V("da"), V("ma")),
                All("b", HermFamily(V("db"), V("mb")), body)))))));
    }

    private static Formula CompoundFormula()
    {
        Formula rows = IndexSets("r", V("m"));
        Formula columns = IndexSets("s", V("n"));
        Formula minor = At(Qualified("Matrix", "det"), At(Qualified("Matrix", "submatrix"), V("c"),
            IncreasingEnumeration("r"), IncreasingEnumeration("s")));
        Formula body = Equal(Typed(LocalCall("compound", V("h"), V("c")), Matrix(rows, columns, Reals)),
            LambdaOf("r", rows, LambdaOf("s", columns, minor)));
        return All("m", Naturals, All("n", Naturals, All("h", Naturals,
            All("c", Matrix(FinOf(V("m")), FinOf(V("n")), Reals), body))));
    }

    private static Formula CmnInfFormula() => All("m", Naturals, All("n", Naturals, All("h", Naturals,
        All("c", Matrix(FinOf(V("m")), FinOf(V("n")), Reals),
            Equal(Typed(LocalCall("cmnInf", V("h"), V("c")), Reals),
                new Formula.Norm(LocalCall("compound", V("h"), V("c"))))))));

    private static Formula BoundFormula()
    {
        Formula larger = At(Qualified("Max", "max"), CastReal(V("da")), CastReal(V("db")));
        Formula smaller = At(Qualified("Min", "min"), CastReal(V("da")), CastReal(V("db")));
        Formula predecessor = Subtract(CastReal(V("h")), Typed(D(1), Reals));
        Formula factors = Multiply(
            Divide(Subtract(larger, Typed(D(1), Reals)), Multiply(larger, predecessor)),
            Divide(Subtract(smaller, Typed(D(1), Reals)), Multiply(smaller, predecessor)));
        Formula value = Multiply(Divide(Typed(D(1), Reals),
            At(Qualified("Real", "sqrt"), Multiply(larger, smaller))),
            Power(factors, Divide(predecessor, Typed(D(2), Reals))));
        return All("da", Naturals, All("db", Naturals, All("h", Naturals,
            Equal(Typed(LocalCall("bound", V("da"), V("db"), V("h")), Reals), value))));
    }

    private static Formula ClaimFormula() => Iff(Local("claim"), ClaimProposition());

    private static Formula ClaimProposition()
    {
        Formula bases = All("a", HermFamily(V("da"), Power(V("da"), D(2))),
            All("b", HermFamily(V("db"), Power(V("db"), D(2))),
                Implies(LocalCall("IsHermBasis", V("a")), Implies(LocalCall("IsHermBasis", V("b")),
                    LE(LocalCall("cmnInf", V("h"), LocalCall("corr", Rho, V("a"), V("b"))),
                        LocalCall("bound", V("da"), V("db"), V("h")))))));
        Formula states = All("ρ", BipartiteMatrix(), Implies(
            At(Qualified("D5", "S3", "Quantum", "QuantumChannels", "IptPptSquaredEquivalence", "IsSeparable"), Rho), bases));
        Formula smaller = At(Qualified("Min", "min"), V("da"), V("db"));
        Formula larger = At(Qualified("Max", "max"), V("da"), V("db"));
        return All("da", Naturals, All("db", Naturals, All("h", Naturals,
            Implies(LE(D(2), V("da")), Implies(LE(D(2), V("db")),
                Implies(LE(Multiply(larger, smaller), Power(V("h"), D(2))),
                    Implies(LE(V("h"), Power(smaller, D(2))), states)))))));
    }

    private static Formula Rho => FormulaDsl.Rho;
    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula V(string name) => name == "ρ" ? Rho : F.Id(name);
    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum", "Entanglement", "Witness",
        "CorrelationMinorNormFNFRefutation", name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula FinOf(Formula size) => At(Qualified("Fin"), size);
    private static Formula Matrix(Formula rows, Formula columns, Formula scalar) =>
        At(Qualified("Matrix"), rows, columns, scalar);
    private static Formula HermFamily(Formula dimension, Formula size) =>
        Arrow(FinOf(size), Matrix(FinOf(dimension), FinOf(dimension), Complexes));
    private static Formula BipartiteMatrix()
    {
        Formula index = At(Qualified("Prod"), FinOf(V("da")), FinOf(V("db")));
        return Matrix(index, index, Complexes);
    }
    private static Formula IndexSets(string name, Formula size) => Seq(OpenBrace,
        Typed(V(name), At(Qualified("Finset"), FinOf(size))), Sp, Slash, Slash, Sp,
        Equal(At(Qualified("Finset", "card"), V(name)), V("h")), CloseBrace);
    private static Formula IncreasingEnumeration(string name) => At(Qualified("DFunLike", "coe"),
        At(Qualified("Finset", "orderEmbOfFin"),
            At(Qualified("Subtype", "val"), V(name)), At(Qualified("Subtype", "property"), V(name))));
    private static Formula Trace(Formula matrix) => At(Qualified("Matrix", "trace"), matrix);
    private static Formula CastReal(Formula value) => Typed(At(Qualified("Nat", "cast"), value), Reals);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, Typed(V(name), type), Sp, Mapsto, Sp, Parenthesized(body)));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LE(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Divide(Formula numerator, Formula denominator) => new Formula.Fraction(numerator, denominator);
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(Parenthesized(value), exponent);
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
}
