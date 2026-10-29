using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class UniformMPSTwoByTwoTraceWordsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/UniformMPSTwoByTwoTraceWords";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Geometry/delazzarimotwaniseynnaeve2022umpsspan");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Traces of binary words in two-by-two matrices have a basis of sorted traces and invariant monomials times the commutator-square scalar.",
        H("A basis for binary two-by-two trace coordinates"),
        Blocks(Describe.Lean(
            DescribeId.Create("uniform-mps-two-by-two-trace-words-coordinate-dimension"),
            DeclarationHandle.Create(Module + ".coordinate_dimension"),
            H("The dimension of the coordinate span"),
            StatementSource.FromAuthor(Disp(CoordinateDimensionFormula())),
            AssessedProvenance.FromRepo(Source),
            Blocks(
                Paragraph(Text(
                    "Let X and Y be complex 2 by 2 matrices. Put s = tr X, t = tr Y, "
                        + "u = det X, v = det Y and w = tr(XY). Give these five invariants weights "
                        + "1, 1, 2, 2 and 2, respectively, and let Rₖ be the complex span of the "
                        + "invariant monomials of weighted degree k, with zero space for negative k. "
                        + "The coordinate functions of the trace parametrization in sigma22-099.tex, "
                        + "lines 219–220, are traces of binary matrix words. The family used here "
                        + "consists of tr(XᵃYⁿ⁻ᵃ) for 0 ≤ a ≤ n and the functions "
                        + "δsᵉ⁽⁰⁾tᵉ⁽¹⁾uᵉ⁽²⁾vᵉ⁽³⁾wᵉ⁽⁴⁾ of total weighted degree n, where "
                        + "δ = w² − stw + s²v + t²u − 4uv has weight four.")),
                Paragraph(Text(
                    "Cayley–Hamilton gives X² = sX − uI and Y² = tY − vI. "
                        + "Its polarized identity gives YX = sY + tX + (w − st)I − XY, "
                        + "and the sandwich identity gives YXY = wY + vX − svI. "
                        + "Induction on the word length therefore writes every word W of length n "
                        + "as aI + bX + cY + dXY, with coefficients in Rₙ, Rₙ₋₁, Rₙ₋₁ and "
                        + "Rₙ₋₂, respectively. The induction starts with I and uses the explicit "
                        + "left-multiplication formulas for X and Y, preserving these degrees.")),
                Paragraph(Text(
                    "Set C = XY − YX. Cyclicity of trace gives tr C = tr(XC) = tr(YC) = 0, "
                        + "whereas direct expansion gives tr(XYC) = δ. Applying these identities "
                        + "to the four-term reduction shows tr(WC) belongs to δRₙ₋₂. "
                        + "An adjacent interchange changes tr(AXYB) by tr(BAC). Consequently the "
                        + "difference between two permuted length-n word traces belongs to δRₙ₋₄. "
                        + "Sorting every binary word gives the inclusion of the coordinate span "
                        + "in the sum of the span of tr(XᵃYⁿ⁻ᵃ) and δRₙ₋₄.")),
                Paragraph(Text(
                    "To obtain the reverse inclusion, start with the constant-coefficient word "
                        + "combination C. The operations Q ↦ XQ + QX, Q ↦ YQ + QY, Q ↦ XQX, "
                        + "Q ↦ YQY and Q ↦ XYQ + QYX send fC to sfC, tfC, ufC, vfC and wfC. "
                        + "They increase every word length by one, one, two, two and two, respectively. "
                        + "Induction on the sum of the exponents constructs, for each invariant "
                        + "monomial f of weight k, a constant-coefficient combination Q of words "
                        + "of length k + 2 with Q = fC. The matrix identity C² = δI then gives "
                        + "tr(QC) = 2δf. This trace is a combination of length-(k + 4) word traces. "
                        + "Since two is nonzero over the complex numbers, δf belongs to their span. "
                        + "Each tr(XᵃYⁿ⁻ᵃ) is itself a length-n word trace.")),
                Paragraph(Text(
                    "The five invariants are algebraically independent. Indeed, any complex "
                        + "quintuple (s,t,u,v,w) with s² ≠ 4u is attained: choose distinct roots λ, μ "
                        + "of z² − sz + u, put X = diag(λ,μ), and set "
                        + "a = (w − μt)/(λ − μ), b = (λt − w)/(λ − μ) and "
                        + "Y = [[a,1],[ab − v,b]]. These matrices have the required invariants. "
                        + "If two polynomials have equal values on every matrix pair, multiply their "
                        + "difference by s² − 4u. The product vanishes on every complex quintuple: "
                        + "on the discriminant-zero set its first factor vanishes, and elsewhere "
                        + "the quintuple is attained. Polynomial extensionality over the infinite "
                        + "field ℂ makes that product the zero polynomial. Since s² − 4u is nonzero "
                        + "and the polynomial ring is a domain, the difference is zero.")),
                Paragraph(Text(
                    "Now consider a linear relation among the proposed family. Evaluate it at "
                        + "X = xI and Y = I. Here δ = 0 and tr(XᵃYⁿ⁻ᵃ) = 2xᵃ, so the relation "
                        + "becomes a polynomial in x with distinct exponents a. Its coefficients "
                        + "vanish, eliminating all coefficients of the sorted traces. The remaining "
                        + "relation is δ times a polynomial in the five invariants. Injectivity of "
                        + "polynomial evaluation at matrix pairs makes this product zero as a "
                        + "polynomial. The polynomial δ is nonzero, as its value at (0,0,0,0,1) "
                        + "is one. Cancellation therefore makes the second factor zero, and its "
                        + "distinct monomials have zero coefficients. This proves independence of "
                        + "the entire family.")),
                Paragraph(Text(
                    "The two inclusions show that this independent family spans the coordinate "
                        + "space. Every exponent in a weight-(n − 4) monomial is at most n, so it "
                        + "can be represented in Fin (n + 1). Its index set is the disjoint union "
                        + "of Fin (n + 1) and exactly the subtype displayed in the formula. "
                        + "The dimension of the span of a finite independent family is its "
                        + "cardinality; the cardinality of that disjoint union is n + 1 plus "
                        + "the stated exponent count. This argument includes n = 0."))),
            DescribeRole.Theorem))));

    private static Formula CoordinateDimensionFormula()
    {
        Formula n = X("n");
        Formula matrices = Arrow(FinOf(D(2)), At(Qualified("Matrix"), FinOf(D(2)), FinOf(D(2)), Complexes()));
        Formula trace = At(Qualified("D5", "S3", "Quantum", "TensorNetworks", "UniformMPSExpectedDimensionRefutation", "traceWord"),
            D(2), D(2), n, X("p"), X("i"));
        Formula family = LambdaOf("i", Arrow(FinOf(n), FinOf(D(2))), LambdaOf("p", matrices, trace));
        Formula span = At(Qualified("Submodule", "span"), Complexes(), At(Qualified("Set", "range"), family));
        Formula dimension = At(Qualified("Module", "finrank"), Complexes(),
            At(Qualified("Subtype"), LambdaOf("x", Arrow(matrices, Complexes()),
                new Formula.Relation(X("x"), FormulaRelationOperator.MemberOf, span))));
        Formula weight = Add(Add(Add(Add(ValueAt(0), ValueAt(1)), Multiply(D(2), ValueAt(2))),
            Multiply(D(2), ValueAt(3))), Multiply(D(2), ValueAt(4)));
        Formula exponents = At(Qualified("Subtype"),
            LambdaOf("e", Arrow(FinOf(D(5)), FinOf(Add(n, D(1)))), Equal(Add(weight, D(4)), n)));
        Formula count = At(Qualified("Fintype", "card"), exponents);
        return All("n", Naturals(), Equal(dimension, Add(Add(n, D(1)), count)));
    }

    private static Formula ValueAt(byte j) => At(Qualified("Fin", "val"), At(X("e"), D(j)));
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
    private static Formula X(string name) => F.Id(name);
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => new Formula.LatexSequence([Open, value, Close]);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula FinOf(Formula n) => At(Qualified("Fin"), n);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
}
