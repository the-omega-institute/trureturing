using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fermionic;

internal sealed class AffineDeterminantAntisymmetricFormsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Fermionic/AffineDeterminantAntisymmetricForms.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Eigenstructure/rouleux2019multimodeentanglement");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Alternating complex polynomials of total degree at most d in d+1 vector variables are scalar affine determinants; with more variables they vanish.",
        H("Low-degree alternating polynomials and the affine determinant"),
        Blocks(
            Definition("is-alternating", "IsAlternating", "Alternation in the vector variables",
                AlternatingFormula(),
                "The indices in Fin r label vectors, and those in Fin d label their coordinates. "
                    + "A permutation acts on the vector index and fixes the coordinate index. "
                    + "IsAlternating requires renaming the polynomial by this action to multiply it by the permutation sign. "
                    + "The sign is first mapped from the units of the integers to the integers by Units.val, then to the complex numbers by Int.cast. "
                    + "DFunLike.coe displays the underlying functions of the permutation equivalence, renaming algebra homomorphism and sign homomorphism. "
                    + "This is the polynomial form of the source's antisymmetry in Section 3, lines 234–248 of 3fermiProc.tex in arXiv:1910.04790v1; no multilinearity is required."),
            Definition("affine-det", "affineDet", "The determinant of differences",
                AffineDetFormula(),
                "Definition 3, lines 251–253, takes the determinant of the d columns obtained by subtracting the first point from each remaining point. "
                    + "Here X(k.succ,j) is coordinate j of the point indexed by k.succ, and X(0,j) is coordinate j of the first point. "
                    + "The row index is j and the column index is k. At d equal to zero the empty determinant is one."),
            Definition("is-nondegenerate", "IsNondegenerate", "Non-degeneracy through affine dimension",
                NondegenerateFormula(),
                "For every family x of d points in the coordinate space Fin d → ℂ, suppose that inserting any first point x₀ makes ω vanish. "
                    + "Non-degeneracy requires the direction of the affine span of those d points to have complex dimension at most d minus two. "
                    + "This expresses the source's condition in lines 262–263 using the smallest affine subspace containing the points. "
                    + "Subtype applied to SetLike.coe of the direction explicitly denotes its underlying vector-space type. "
                    + "The subtraction d minus two is natural-number subtraction; the non-degeneracy conclusion below assumes d at least two."),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Vanishing, classification and non-degeneracy"),
                StatementSource.FromAuthor(Disp(ResultFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Represent a monomial by its exponent array m, with one row in ℕ^d for each vector variable. "
                            + "Alternation relates the coefficient at a permuted array to the original coefficient multiplied by the permutation sign. "
                            + "If two rows coincide, their transposition fixes the monomial and negates its coefficient. "
                            + "Over ℂ that coefficient is zero. Thus every monomial with nonzero coefficient has pairwise distinct exponent rows.")),
                    Paragraph(Text(
                        "The total exponent sum is the sum of the row sums. Among distinct rows at most one is zero, and each remaining row contributes at least one. "
                            + "Consequently r distinct rows have total exponent sum at least r minus one. "
                            + "With d+1 rows and total exponent sum at most d, there must be one zero row and all other row sums must equal one. "
                            + "Those other rows are distinct coordinate unit vectors, so they comprise all d unit vectors. "
                            + "Every such monomial is therefore a permutation of the monomial with zero row at index zero and the kth unit row at index k.succ.")),
                    Paragraph(Text(
                        "If r is at least d+2, the row-count bound contradicts total degree at most d for any monomial in the support. "
                            + "Every coefficient must vanish, proving the first conjunct.")),
                    Paragraph(Text(
                        "To prove alternation of the affine determinant, adjoin a row of ones above the matrix of point coordinates. "
                            + "Transpose this bordered matrix and subtract its first row from every other row. "
                            + "These row operations preserve its determinant; expansion along the first column leaves the transpose of the matrix of differences. "
                            + "Thus the bordered determinant equals the affine determinant. "
                            + "Renaming the point variables permutes the columns of the bordered matrix, multiplying its determinant by the permutation sign. "
                            + "Expanding the determinant of differences gives a sum of products of d linear polynomials, so its total degree is at most d. "
                            + "This proves the second conjunct.")),
                    Paragraph(Text(
                        "The coefficient of the distinguished monomial, the product of X(k.succ,k) over k in Fin d, is one in the affine determinant. "
                            + "To see this, retain only these d variables and set every other variable to zero. "
                            + "The matrix of differences becomes diagonal, and its determinant is their product; the coefficient is preserved by this restriction.")),
                    Paragraph(Text(
                        "Let c be the coefficient of that monomial in f, and subtract c times the affine determinant. "
                            + "The difference is still alternating, has total degree at most d, and has zero coefficient at the distinguished monomial. "
                            + "Every monomial in its support would be a permutation of that monomial, and the coefficient relation would force its coefficient to be zero. "
                            + "Hence the difference vanishes, proving the third conjunct with this c.")),
                    Paragraph(Text(
                        "For the fourth conjunct let d be at least two, and suppose the evaluated affine determinant vanishes for every first point x₀. "
                            + "The dimension bound for the direction of the affine span of d points is equivalent to their failure to be affinely independent. "
                            + "Assume instead that the d points are affinely independent. "
                            + "Their affine span is a proper affine subspace of the d-dimensional ambient affine space, so choose x₀ outside it. "
                            + "Inserting x₀ gives d+1 affinely independent points. "
                            + "Their d differences from x₀ are linearly independent, so the square matrix having these columns has nonzero determinant. "
                            + "Evaluation of the polynomial affine determinant is exactly this matrix determinant, contradicting the assumed vanishing. "
                            + "The direction dimension is therefore at most d minus two.")),
                    Paragraph(Text(
                        "The four conjuncts give a scalar-polynomial reading of the two conjectures in lines 266–269. "
                            + "The total-degree bound includes homogeneous polynomials of degree d. "
                            + "The separate collapse conjecture in lines 271–272 is outside these statements."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Definition(string id, string declaration, string title,
        Formula formula, string prose) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula AlternatingFormula()
    {
        Formula permutation = At(Qualified("Equiv", "prodCongr"), X("σ"),
            At(Qualified("Equiv", "refl"), FinOf(X("d"))));
        Formula rename = UnderlyingFunction(At(Qualified("MvPolynomial", "rename"),
            UnderlyingFunction(permutation)));
        Formula sign = At(UnderlyingFunction(Qualified("Equiv", "Perm", "sign")), X("σ"));
        Formula integerSign = Typed(At(Qualified("Units", "val"), sign), Integers());
        Formula complexSign = Typed(At(Qualified("Int", "cast"), integerSign), Complexes());
        return All("r", Naturals(), All("d", Naturals(), All("f", Polynomial(X("r"), X("d")),
            Equivalence(LocalCall("IsAlternating", X("f")),
                All("σ", At(Qualified("Equiv", "Perm"), FinOf(X("r"))),
                    Equal(At(rename, X("f")), Smul(complexSign, X("f"))))))));
    }

    private static Formula AffineDetFormula()
    {
        Formula entry = Subtract(
            At(Qualified("MvPolynomial", "X"), Pair(At(Qualified("Fin", "succ"), X("k")), X("j"))),
            At(Qualified("MvPolynomial", "X"), Pair(Typed(D(0), FinOf(Add(X("d"), D(1)))), X("j"))));
        return All("d", Naturals(), Equal(
            Typed(LocalCall("affineDet", X("d")), Polynomial(Add(X("d"), D(1)), X("d"))),
            At(Qualified("Matrix", "det"), LambdaOf("j", FinOf(X("d")),
                LambdaOf("k", FinOf(X("d")), entry)))));
    }

    private static Formula NondegenerateFormula()
    {
        Formula direction = At(Qualified("AffineSubspace", "direction"),
            At(Qualified("affineSpan"), Complexes(), At(Qualified("Set", "range"), X("x"))));
        Formula directionType = At(Qualified("Subtype"), At(Qualified("SetLike", "coe"), direction));
        Formula vanishing = All("x₀", VectorType(), Equal(
            At(X("ω"), At(Qualified("Fin", "cons"), X("x₀"), X("x"))), Typed(D(0), Complexes())));
        return All("d", Naturals(), All("ω", Arrow(PointFamily(), Complexes()),
            Equivalence(LocalCall("IsNondegenerate", X("d"), X("ω")),
                All("x", Arrow(FinOf(X("d")), VectorType()), Imp(vanishing,
                    LE(At(Qualified("Module", "finrank"), Complexes(), directionType),
                        Typed(Subtract(X("d"), D(2)), Naturals())))))));
    }

    private static Formula ResultFormula()
    {
        Formula vanishing = All("d", Naturals(), All("r", Naturals(), Imp(LE(Add(X("d"), D(2)), X("r")),
            All("f", Polynomial(X("r"), X("d")), Imp(LocalCall("IsAlternating", X("f")),
                Imp(LE(TotalDegree(X("f")), X("d")),
                    Equal(X("f"), Typed(D(0), Polynomial(X("r"), X("d"))))))))));
        Formula determinant = All("d", Naturals(), Conjunction(
            LocalCall("IsAlternating", LocalCall("affineDet", X("d"))),
            LE(TotalDegree(LocalCall("affineDet", X("d"))), X("d"))));
        Formula classification = All("d", Naturals(),
            All("f", Polynomial(Add(X("d"), D(1)), X("d")),
                Imp(LocalCall("IsAlternating", X("f")), Imp(LE(TotalDegree(X("f")), X("d")),
                    Some("c", Complexes(), Equal(X("f"), Smul(X("c"), LocalCall("affineDet", X("d")))))))));
        Formula coordinate = LambdaOf("p", Product(FinOf(Add(X("d"), D(1))), FinOf(X("d"))),
            At(X("y"), At(Qualified("Prod", "fst"), X("p")), At(Qualified("Prod", "snd"), X("p"))));
        Formula evaluation = LambdaOf("y", PointFamily(),
            At(UnderlyingFunction(At(Qualified("MvPolynomial", "eval"), coordinate)),
                LocalCall("affineDet", X("d"))));
        Formula nondegeneracy = All("d", Naturals(), Imp(LE(D(2), X("d")),
            LocalCall("IsNondegenerate", X("d"), evaluation)));
        return Conjunction(vanishing, Conjunction(determinant, Conjunction(classification, nondegeneracy)));
    }

    private static Formula X(string name) => name switch
    {
        "σ" => SigmaLower,
        "ω" => Omega,
        "x₀" => new Formula.Subscript(F.Id("x"), D(0)),
        _ => F.Id(name),
    };
    private static Formula Qualified(params string[] parts)
    {
        Formula value = F.Id(parts[0]);
        for (int i = 1; i < parts.Length; i++) value = Seq(value, Dot, F.Id(parts[i]));
        return Seq(Operatorname, Grp(value));
    }
    private static Formula LocalCall(string name, params Formula[] arguments) =>
        At(Qualified("D5", "S3", "Quantum", "Fermionic", "AffineDeterminantAntisymmetricForms", name), arguments);
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula UnderlyingFunction(Formula value) => At(Qualified("DFunLike", "coe"), value);
    private static Formula Parenthesized(Formula value) => new Formula.LatexSequence([Open, value, Close]);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Product(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Times, Sp, Parenthesized(b));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => new Formula.Integers();
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula FinOf(Formula size) => At(Qualified("Fin"), size);
    private static Formula Polynomial(Formula r, Formula d) =>
        At(Qualified("MvPolynomial"), Product(FinOf(r), FinOf(d)), Complexes());
    private static Formula VectorType() => Arrow(FinOf(X("d")), Complexes());
    private static Formula PointFamily() => Arrow(FinOf(Add(X("d"), D(1))), VectorType());
    private static Formula TotalDegree(Formula f) => At(Qualified("MvPolynomial", "totalDegree"), f);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Smul(Formula scalar, Formula polynomial) =>
        Seq(Parenthesized(scalar), Sp, Cdot, Sp, Parenthesized(polynomial));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula LE(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Conjunction(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Equivalence(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
}
