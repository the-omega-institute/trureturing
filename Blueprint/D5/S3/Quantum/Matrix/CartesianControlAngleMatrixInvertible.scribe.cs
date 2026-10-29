using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class CartesianControlAngleMatrixInvertibleDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Matrix/CartesianControlAngleMatrixInvertible.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Eigenstructure/jiangklcodimatteo2025cube");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The real angle matrix of a finite Cartesian control set is invertible for every pair of enumerations and every choice of coordinate dimensions.",
        H("Invertibility of Cartesian-control angle matrices"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("angle-matrix"),
                DeclarationHandle.Create(Prefix + "angleMatrix"),
                H("The angle matrix for two enumerations"),
                StatementSource.FromAuthor(Disp(AngleMatrixFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "A control word chooses a digit in Fin (d l) at every coordinate l in Fin k. "
                    + "The equivalences b and g enumerate all such words by Fin of the product of the dimensions. "
                    + "For row i and column j, each coordinate contributes minus one exactly when the natural digit "
                    + "of b i is positive and is at most the corresponding natural digit of g j; otherwise it contributes one. "
                    + "The matrix entry is the product of these real signs. Equiv.toFun makes the use of an equivalence "
                    + "as a function explicit, and Fin.val converts each digit to a natural number. "
                    + "This is the matrix of equation (5), subsec_3a_uniform-rotations.tex, lines 38–49, "
                    + "with arbitrary coordinate dimensions and arbitrary enumerations, as used for the two sequences "
                    + "in subsec_3c_restricted-rotations.tex, lines 34–36."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("Invertibility for every finite Cartesian product"),
                StatementSource.FromAuthor(Disp(Equivalence(Local("claim"), InvertibilityFormula()))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every natural k, every family d of natural dimensions, and every pair of equivalences b and g "
                    + "enumerating the Cartesian product, the angle matrix is a unit in the real square-matrix ring. "
                    + "Thus it has a two-sided matrix inverse. The conjecture in subsec_3c_restricted-rotations.tex, "
                    + "lines 38–46, concerns the sequences produced by the source's particular construction. "
                    + "The assertion here applies to every pair of enumerations. It includes dimensions zero and one "
                    + "and the empty family of coordinates, without a positivity assumption. "
                    + "The sequencing algorithms of app_3c_sequencers.tex, lines 31–40, are not part of this assertion."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The angle matrix is invertible"),
                StatementSource.FromAuthor(Disp(InvertibilityFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "First consider the real square matrix on Fin m whose entry at r,s is minus one when "
                        + "0 < r ≤ s and one otherwise, using the natural values of the indices. "
                        + "Multiply it on the left by the row transformation that keeps row zero and replaces every "
                        + "positive row r by half of row zero minus half of row r. "
                        + "The resulting entry at r,s is one when r ≤ s and zero otherwise: "
                        + "row zero consists of ones, and for positive r the difference is one exactly when r ≤ s. "
                        + "This is the zeta matrix of the linearly ordered set Fin m.")),
                    Paragraph(Text(
                        "The zeta matrix is upper triangular and has every diagonal entry equal to one, "
                        + "so its determinant is one. Taking determinants of the preceding product shows that "
                        + "the determinant of the row transformation times the determinant of the sign matrix is one. "
                        + "The latter determinant is therefore a unit. These determinant identities include m equal to zero, "
                        + "where the diagonal product is empty.")),
                    Paragraph(Text(
                        "Next index rows and columns by control words and form the product matrix whose entry at r,s "
                        + "is the product, over l, of the one-coordinate sign-matrix entries at r l,s l. "
                        + "Form a second matrix by taking the same coordinatewise product of the inverses of those sign matrices. "
                        + "To multiply the second matrix by the first, sum over the intermediate control word r. "
                        + "Distribute the products inside that sum and factor the sum over all words into the product "
                        + "of the sums over each individual digit. Each such sum is an entry of the corresponding "
                        + "one-coordinate inverse times its original matrix, hence is one when the two endpoint digits "
                        + "agree and zero otherwise. The product is one exactly when all endpoint digits agree. "
                        + "Function extensionality identifies this condition with equality of the endpoint words, "
                        + "so the second matrix is a left inverse of the product matrix.")),
                    Paragraph(Text(
                        "A square matrix with a left inverse has unit determinant, and a square matrix whose determinant "
                        + "is a unit is itself a unit. Finally, the angle matrix is the submatrix of this product matrix "
                        + "obtained by reindexing its rows through b and its columns through g. "
                        + "Both maps are equivalences, so this independent reindexing preserves being a unit. "
                        + "This proves the assertion for all k,d,b,g, including empty index types and empty products."))),
                DescribeRole.Theorem))));

    private static Formula AngleMatrixFormula()
    {
        Formula bDigit = NaturalDigit("b", "i");
        Formula gDigit = NaturalDigit("g", "j");
        Formula condition = Conjunction(LessThan(Typed(D(0), Naturals()), bDigit),
            LessThanOrEqual(bDigit, gDigit));
        Formula sign = At(Qualified("ite"), Parenthesized(condition),
            new Formula.Negate(Typed(D(1), Reals())), Typed(D(1), Reals()));
        Formula entries = LambdaOf("i", Index(), LambdaOf("j", Index(),
            Product("l", FinOf(X("k")), sign)));
        return Parameters(Equal(Typed(AngleMatrix(),
            At(Qualified("Matrix"), Index(), Index(), Reals())), Parenthesized(entries)));
    }

    private static Formula InvertibilityFormula() => Parameters(At(Qualified("IsUnit"), AngleMatrix()));
    private static Formula AngleMatrix() => At(Local("angleMatrix"), X("d"), X("b"), X("g"));
    private static Formula NaturalDigit(string enumeration, string index) =>
        Typed(At(Qualified("Fin", "val"),
            At(Qualified("Equiv", "toFun"), X(enumeration), X(index), X("l"))), Naturals());
    private static Formula Parameters(Formula body) => All("k", Naturals(),
        All("d", Arrow(FinOf(X("k")), Naturals()),
            All("b", Enumerations(), All("g", Enumerations(), body))));
    private static Formula Index() => FinOf(Product("l", FinOf(X("k")), At(X("d"), X("l"))));
    private static Formula Words() => Seq(Typed(X("l"), FinOf(X("k"))), Sp, To, Sp,
        FinOf(At(X("d"), X("l"))));
    private static Formula Enumerations() => At(Qualified("Equiv"), Index(), Parenthesized(Words()));
    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum", "Matrix",
        "CartesianControlAngleMatrixInvertible", name);
    private static Formula X(string name) => F.Id(name);
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
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula FinOf(Formula size) => At(Qualified("Fin"), size);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Product(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Prod, Seq(X(name), Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LessThan(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula LessThanOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Conjunction(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
