using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FluidDynamics.Vortices;

internal sealed class InverseChordCirculantDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FluidDynamics/Vortices/InverseChordCirculant.";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/FluidDynamics/barrykevrekidis2013vortex");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fourier analysis of inverse squared chord weights gives the alternating block-product spectrum.",
        H("Inverse squared chord circulants"), Blocks(
            Node("weights", "weights", "The interaction weights", WeightsFormula(),
                "Off the diagonal the weight is the reciprocal squared distance between unit vertices of a regular 2m-gon. "
                    + "The diagonal is zero. These weights are constructed from the polygon interactions of Barry–Kevrekidis, "
                    + "Section 4.1 (arXiv:1306.1545v2, TeX lines 552–577).", DescribeRole.Definition),
            Node("charge-matrix", "chargeMatrix", "The alternating sign matrix", ChargeMatrixFormula(),
                "The zero-size matrix is zero. At a successor m=n+1, indexParity (2n+1) 2 constructs the diagonal "
                    + "alternating-sign matrix. The next identity identifies its entries without a case distinction.", DescribeRole.Definition),
            Node("charge-matrix-diagonal", "chargeMatrix_diagonal", "The diagonal charge identity", ChargeDiagonalFormula(),
                "The charge matrix is diagonal with jth entry (−1)^(j.val+2). For m=0 there is no index; "
                    + "for m=n+1 the identity follows from the diagonal definition of indexParity and commutativity of natural addition.", DescribeRole.Theorem),
            Node("diagonal-weight", "diagonalWeight", "The alternating Fourier value", DiagonalWeightFormula(),
                "For m≥3, this scalar is the half-period Fourier value of the inverse-squared-chord weights. The product 2m "
                    + "is first formed in the natural numbers and then cast to the reals; m is also cast before squaring.", DescribeRole.Definition),
            Node("block-b", "blockB", "The upper-right block", BlockFormula("blockB", false),
                "Subtract the interaction matrix from diagonalWeight times the identity, then multiply on the right by the charge matrix.", DescribeRole.Definition),
            Node("block-c", "blockC", "The lower-left block", BlockFormula("blockC", true),
                "The second block has the same form with diagonalWeight increased by one before scalar multiplication.", DescribeRole.Definition),
            Node("alternating-weight-sum", "alternating_weight_sum", "The signed row sum", AlternatingSumFormula(),
                "For m≥3, the charge-weighted sum along row j equals the jth charge times diagonalWeight m. "
                    + "Translate the cyclic difference j−k to the summation index. Alternating signs are the half-period character, "
                    + "so the sum is the Fourier coefficient in mode m. Evaluating that coefficient yields the scalar.", DescribeRole.Theorem),
            Node("gamma", "gamma", "The paired mode value", GammaFormula(),
                "For positive m, the minimum of the two natural distances is the folded cyclic distance r of the residue k from zero. "
                    + "The formula is defined for every natural m. Cast m and r to real numbers before computing (m−r)²(r²−2)/4. "
                    + "The subtraction 2m−k.val inside the minimum remains natural subtraction.", DescribeRole.Definition),
            Node("product-spectrum", "product_spectrum", "The block-product determinant", ProductFormula(),
                "Reindex the matrices by ZMod (2m) and include their real entries in the complex numbers. The weight matrix is circulant. "
                    + "Conjugating it by the diagonal charge matrix multiplies its cyclic kernel by alternating signs, while the square of the charge matrix is the identity. "
                    + "Thus blockC times blockB becomes the product of two circulants, with scalar identity terms diagonalWeight+1 and diagonalWeight. "
                    + "The common Fourier matrix has nonzero determinant and diagonalizes both circulants; taking determinants gives the product of their mode factors. "
                    + "The inverse-squared-chord Fourier value at mode k is ((2m)²−1)/12−k.val(2m−k.val)/2. "
                    + "To obtain it, the quadratic mode function has periodic second difference 1−2m at zero and 1 elsewhere, "
                    + "and its sum is zero by the finite sums of first and second powers. Fourier transformation of that difference "
                    + "equation multiplies by −4sin²(πl.val/(2m)); division at nonzero l and the zero-sum identity at l=0 identify the kernel. "
                    + "Fourier inversion then gives all its Fourier values. Alternating signs shift mode k to k+m. "
                    + "Multiplying the two resulting real factors, separating k.val<m from k.val≥m, gives gamma m (k+m). "
                    + "Finally, translating the product index by m and using injectivity of the real inclusion proves the stated real determinant identity.", DescribeRole.Theorem))));

    private static Formula WeightsFormula()
    {
        Formula size = Size();
        Formula angle = Divide(Multiply(Qualified("Real", "pi"), Subtract(CastReal(FinVal(X("j"))), CastReal(FinVal(X("k"))))), Multiply(D(2), CastReal(X("m"))));
        Formula weight = Divide(Typed(D(1), Reals()), Multiply(D(4), Power(At(Qualified("Real", "sin"), angle), D(2))));
        return All("m", Naturals(), All("j", FinOf(size), All("k", FinOf(size),
            Equal(LocalCall("weights", X("m"), X("j"), X("k")), If(Equal(X("j"), X("k")), Typed(D(0), Reals()), weight)))));
    }

    private static Formula ChargeMatrixFormula()
    {
        Formula zeroMatrix = Typed(D(0), MatrixType(D(0)));
        Formula successor = LambdaOf("n", Naturals(), At(Qualified("D5", "S3", "Quantum", "Algebra", "ZeitlinSixJ", "Inverse", "indexParity"),
            Add(Multiply(D(2), X("n")), D(1)), D(2)));
        return All("m", Naturals(), Equal(LocalCall("chargeMatrix", X("m")), At(Qualified("Nat", "casesOn"), X("m"), zeroMatrix, successor)));
    }

    private static Formula ChargeDiagonalFormula() => All("m", Naturals(), Equal(LocalCall("chargeMatrix", X("m")),
        At(Qualified("Matrix", "diagonal"), LambdaOf("j", FinOf(Size()), Sign(X("j"))))));

    private static Formula DiagonalWeightFormula() => All("m", Naturals(), Equal(LocalCall("diagonalWeight", X("m")),
        Subtract(Divide(Subtract(Power(CastReal(Typed(Size(), Naturals())), D(2)), D(1)), D(1, 2)), Divide(Power(CastReal(X("m")), D(2)), D(2)))));

    private static Formula BlockFormula(string name, bool increment)
    {
        Formula a = LocalCall("diagonalWeight", X("m"));
        if (increment) a = Add(a, Typed(D(1), Reals()));
        return All("m", Naturals(), Equal(LocalCall(name, X("m")),
            Multiply(Subtract(Smul(a, Identity()), LocalCall("weights", X("m"))), LocalCall("chargeMatrix", X("m")))));
    }

    private static Formula AlternatingSumFormula() => All("m", Naturals(), Implication(LE(D(3), X("m")),
        All("j", FinOf(Size()), Equal(SumOver("k", FinOf(Size()), Multiply(Sign(X("k")), LocalCall("weights", X("m"), X("j"), X("k")))),
            Multiply(Sign(X("j")), LocalCall("diagonalWeight", X("m")))))));

    private static Formula GammaFormula()
    {
        Formula residue = At(Qualified("ZMod", "val"), X("k"));
        Formula r = At(Qualified("min"), residue, Typed(Subtract(Size(), residue), Naturals()));
        Formula value = Divide(Multiply(Power(Subtract(CastReal(X("m")), CastReal(X("r"))), D(2)),
            Subtract(Power(CastReal(X("r")), D(2)), D(2))), D(4));
        Formula body = Seq(Qualified("let"), Sp, Typed(X("r"), Naturals()), Sp, Eq, Sp, r, Sp, Qualified("in"), Sp, value);
        return All("m", Naturals(), All("k", At(Qualified("ZMod"), Size()), Equal(LocalCall("gamma", X("m"), X("k")), body)));
    }

    private static Formula ProductFormula()
    {
        Formula determinant = At(Qualified("Matrix", "det"), Subtract(Smul(X("y"), Identity()),
            Multiply(LocalCall("blockC", X("m")), LocalCall("blockB", X("m")))));
        Formula product = Seq(new Formula.Subscript(Prod, Seq(X("k"), Colon, Sp, At(Qualified("ZMod"), Size()))), Sp,
            Parenthesized(Subtract(X("y"), LocalCall("gamma", X("m"), X("k")))));
        return All("m", Naturals(), Seq(OpenBracket, At(Qualified("NeZero"), Size()), CloseBracket, Sp,
            Implication(LE(D(3), X("m")), All("y", Reals(), Equal(determinant, product)))));
    }

    private static DocumentBlock Node(string id, string name, string title, Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("inverse-chord-circulant-" + id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);
    private static Formula Local(string name) => Qualified("D5", "S3", "FluidDynamics", "Vortices", "InverseChordCirculant", name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula Size() => Multiply(D(2), X("m"));
    private static Formula MatrixType(Formula size) => At(Qualified("Matrix"), FinOf(size), FinOf(size), Reals());
    private static Formula Identity() => Typed(D(1), MatrixType(Size()));
    private static Formula FinVal(Formula value) => At(Qualified("Fin", "val"), value);
    private static Formula Sign(Formula j) => Power(Negate(Typed(D(1), Reals())), Add(FinVal(j), D(2)));

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
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula CastReal(Formula value) => Typed(value, Reals());
    private static Formula FinOf(Formula size) => At(Qualified("Fin"), size);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) => Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Implication(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Subtract(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Multiply(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Smul(Formula left, Formula right) => Seq(Parenthesized(left), Sp, Cdot, Sp, Parenthesized(right));
    private static Formula Divide(Formula left, Formula right) => new Formula.Fraction(left, right);
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(Parenthesized(value), exponent);
    private static Formula Negate(Formula value) => new Formula.Negate(Parenthesized(value));
    private static Formula If(Formula condition, Formula yes, Formula no) => At(Qualified("ite"), condition, yes, no);
    private static Formula SumOver(string name, Formula type, Formula body) => Seq(new Formula.Subscript(Sum, Seq(X(name), Colon, Sp, type)), Sp, Parenthesized(body));
}
