using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class UniformMPSExpectedDimensionRefutationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/UniformMPSExpectedDimensionRefutation";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Geometry/czaplinskimichalekseynnaeve2023umps");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two-site uniform matrix product states with bond dimension two and five symbols miss the expected dimension.",
        H("A dimension defect for uniform matrix product states"),
        Blocks(
            Node("trace-word", "traceWord", "Trace coefficients of a matrix word", TraceWordFormula(),
                AssessedProvenance.FromLiterature(Source),
                "For a family m of d complex b by b matrices and a word i of length n, take the trace of "
                    + "the product m(i(0)) through m(i(n - 1)), in that order. These are the coefficients "
                    + "of the tensor T_n in uMPS-final.tex, lines 180–185. List.ofFn lists the sites in order; "
                    + "its product is the identity matrix when n is zero. The definition permits all natural "
                    + "b, d and n, while the source assumes that all three are positive."),
            Node("umps", "uMPS", "The image of the trace-word map", UMPSFormula(),
                AssessedProvenance.FromLiterature(Source),
                "The set uMPS b d n consists of all coefficient functions obtained by varying the same "
                    + "family of matrices at every site. The ambient space is the space of complex functions "
                    + "on words Fin n → Fin d. This is the image description of uniform periodic matrix "
                    + "product states in uMPS-final.tex, lines 187–193, with no normalization condition."),
            Node("variety-dim", "varietyDim", "Dimension through the vanishing ideal", VarietyDimFormula(),
                AssessedProvenance.FromRepo(Source),
                "For a set s of complex-valued functions on any type σ, form the polynomial ring with "
                    + "one variable for each element of σ and quotient by all polynomials vanishing on s. "
                    + "The Krull dimension of this coordinate ring defines varietyDim s, with values in "
                    + "WithBot ℕ∞. For finite σ this measures the dimension of the Zariski closure, so the "
                    + "image itself need not be closed. The source considers this closure in uMPS-final.tex, "
                    + "line 211, and its dimension in lines 272–273."),
            Node("claim", "claim", "Expected dimension for every positive triple", ClaimFormula(),
                AssessedProvenance.FromRepo(Source),
                "For every positive b, d and n, the asserted dimension is the smaller of (d - 1)b² + 1 "
                    + "and the complex dimension of the fixed subspace of cyclic rotation. Here rotation "
                    + "sends a word i to i composed with finRotate n; a coefficient function is fixed "
                    + "exactly when its value is unchanged by this operation. The rotation equivalence "
                    + "is used through its underlying function, and the fixed submodule through its "
                    + "underlying subtype of coefficient functions. The minimum is computed "
                    + "in ℕ and then cast to WithBot ℕ∞. This expresses the expected-dimension equality "
                    + "of uMPS-final.tex, lines 299–305, for every triple as in Conjecture 2.14, "
                    + "lines 311–313; the cyclic subspace is described at line 209."),
            Describe.Lean(
                DescribeId.Create("uniform-mps-expected-dimension-result"),
                DeclarationHandle.Create(Module + ".result"),
                H("A determinant forces a strict dimension defect"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Let U be the set of pairs (a,b) in Fin 5 × Fin 5 with a ≤ b, and let the sorted "
                            + "pair associated to (i,j) be (min(i,j),max(i,j)). There are 15 elements of U. "
                            + "A function v : U → ℂ determines a two-site coefficient function by sending "
                            + "a word i to v at the sorted pair of i(0) and i(1). Rotation interchanges "
                            + "the two entries, so this coefficient function is fixed. This construction "
                            + "is complex linear and injective: evaluation on the word (a,b) recovers v(a,b) "
                            + "for every (a,b) in U. Consequently the cyclic fixed subspace has dimension "
                            + "at least 15.")),
                    Paragraph(Text(
                        "For five complex 2 by 2 matrices m(i), the two-site coefficients are "
                            + "S(i,j) = tr(m(i)m(j)). Define X(i,(a,b)) = m(i)(a,b) and "
                            + "Y((a,b),j) = m(j)(b,a), with (a,b) in Fin 2 × Fin 2. Expanding the trace "
                            + "as a double sum gives S = XY. The linear map represented by Y has "
                            + "a five-dimensional domain and a four-dimensional codomain, so it has "
                            + "a nonzero kernel vector. The same vector is killed by XY, and therefore "
                            + "det S = 0.")),
                    Paragraph(Text(
                        "Write A for the coordinate ring of uMPS 2 5 2 and x(i,j) for the variable "
                            + "indexed by the two-letter word (i,j). Since tr(m(i)m(j)) = tr(m(j)m(i)), "
                            + "each difference x(i,j) - x(j,i) belongs to the vanishing ideal. There is "
                            + "a complex algebra homomorphism ψ from P = ℂ[y(p) : p in U] to A sending "
                            + "y(a,b) to the class of x(a,b). The symmetry relations show that y at "
                            + "the sorted pair of (i,j) maps to the class of x(i,j), including when "
                            + "i > j. Thus every coordinate variable is in the image. Induction on "
                            + "polynomials, using constants, addition and multiplication by a variable, "
                            + "then proves that ψ is surjective.")),
                    Paragraph(Text(
                        "In P take Δ to be the determinant of the symmetric 5 by 5 matrix whose "
                            + "(i,j) entry is y at the sorted pair of (i,j). Evaluating the diagonal "
                            + "variables at 1 and the other variables at 0 gives the identity matrix "
                            + "and hence Δ = 1 under this evaluation. Therefore Δ is a nonzero "
                            + "polynomial. Determinants commute with algebra homomorphisms; ψ(Δ) "
                            + "is the class of det(x(i,j)). Evaluating this determinant at any "
                            + "trace-word image gives det S = 0, so it belongs to the vanishing "
                            + "ideal and ψ(Δ) = 0.")),
                    Paragraph(Text(
                        "The polynomial ring P is a domain, so the nonzero element Δ is a "
                            + "nonzero divisor. The Krull-dimension inequality for a surjective ring "
                            + "homomorphism killing such an element gives dim A + 1 ≤ dim P. "
                            + "There are 15 variables and ℂ has Krull dimension zero, so dim P = 15. "
                            + "Cancellation in WithBot ℕ∞ yields varietyDim (uMPS 2 5 2) ≤ 14.")),
                    Paragraph(Text(
                        "Suppose claim holds and apply it to b = 2, d = 5 and n = 2, which "
                            + "are all positive. The first entry of its minimum is (5 - 1)2² + 1 = 17, "
                            + "and the cyclic-space bound makes the second entry at least 15. "
                            + "Thus the minimum is at least 15 in ℕ. Casting this inequality to "
                            + "WithBot ℕ∞ and substituting the asserted dimension equality gives "
                            + "15 ≤ varietyDim (uMPS 2 5 2) ≤ 14, a contradiction."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, Formula formula,
        AssessedProvenance provenance, string prose) =>
        Describe.Lean(DescribeId.Create("uniform-mps-expected-dimension-" + id),
            DeclarationHandle.Create(Module + "." + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula TraceWordFormula()
    {
        Formula matrices = Arrow(FinOf(X("d")), MatrixType(X("b")));
        Formula list = At(Qualified("List", "ofFn"),
            LambdaOf("k", FinOf(X("n")), At(X("m"), At(X("i"), X("k")))));
        Formula trace = At(Qualified("Matrix", "trace"), At(Qualified("List", "prod"), list));
        return DimensionBinders(All("m", matrices, All("i", Words(X("n"), X("d")),
            Equal(Typed(LocalCall("traceWord", X("b"), X("d"), X("n"), X("m"), X("i")),
                Complexes()), trace))));
    }

    private static Formula UMPSFormula() => DimensionBinders(Equal(
        Typed(LocalCall("uMPS", X("b"), X("d"), X("n")),
            SetOf(Arrow(Words(X("n"), X("d")), Complexes()))),
        At(Qualified("Set", "range"), LocalCall("traceWord", X("b"), X("d"), X("n")))));

    private static Formula VarietyDimFormula()
    {
        Formula polynomials = At(Qualified("MvPolynomial"), X("σ"), Complexes());
        Formula ideal = At(Qualified("MvPolynomial", "vanishingIdeal"), Complexes(), X("s"));
        Formula quotient = Seq(Parenthesized(polynomials), Sp, Slash, Sp, Parenthesized(ideal));
        return All("σ", Seq(Qualified("Type"), Star),
            All("s", SetOf(Arrow(X("σ"), Complexes())),
                Equal(Typed(LocalCall("varietyDim", X("s")), DimensionType()),
                    At(Qualified("ringKrullDim"), quotient))));
    }

    private static Formula ClaimFormula()
    {
        Formula rotation = LambdaOf("i", Words(X("n"), X("d")),
            At(Qualified("Function", "comp"), X("i"),
                At(Qualified("Equiv", "toFun"), At(Qualified("finRotate"), X("n")))));
        Formula fixedSpace = At(Qualified("LinearMap", "fixedSubmodule"),
            At(Qualified("LinearMap", "funLeft"), Complexes(), Complexes(), rotation));
        Formula fixedType = At(Qualified("Subtype"),
            LambdaOf("x", Arrow(Words(X("n"), X("d")), Complexes()),
                new Formula.Relation(X("x"), FormulaRelationOperator.MemberOf, fixedSpace)));
        Formula parameterBound = Add(Multiply(Subtract(X("d"), D(1)),
            new Formula.Power(X("b"), D(2))), D(1));
        Formula minimum = Typed(At(Qualified("min"), parameterBound,
            At(Qualified("Module", "finrank"), Complexes(), fixedType)), Naturals());
        Formula dimension = LocalCall("varietyDim", LocalCall("uMPS", X("b"), X("d"), X("n")));
        Formula equality = Equal(dimension,
            Typed(At(Qualified("Nat", "cast"), minimum), DimensionType()));
        Formula positive = Imp(Less(D(0), X("b")),
            Imp(Less(D(0), X("d")), Imp(Less(D(0), X("n")), equality)));
        return Iff(Local("claim"), DimensionBinders(positive));
    }

    private static Formula DimensionBinders(Formula body) =>
        All("b", Naturals(), All("d", Naturals(), All("n", Naturals(), body)));
    private static Formula MatrixType(Formula b) =>
        At(Qualified("Matrix"), FinOf(b), FinOf(b), Complexes());
    private static Formula Words(Formula n, Formula d) => Arrow(FinOf(n), FinOf(d));
    private static Formula DimensionType() =>
        At(Qualified("WithBot"), new Formula.Subscript(Naturals(), Infty));
    private static Formula SetOf(Formula type) => At(Qualified("Set"), type);
    private static Formula FinOf(Formula n) => At(Qualified("Fin"), n);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula X(string name) => name == "σ" ? SigmaLower : F.Id(name);
    private static Formula Local(string name) =>
        Qualified("D5", "S3", "Quantum", "TensorNetworks", "UniformMPSExpectedDimensionRefutation", name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
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
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.TypeArrow(Parenthesized(left), Parenthesized(right));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
}
