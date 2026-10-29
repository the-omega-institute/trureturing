using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class UniformMPSTwoByTwoLinearSpanDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/UniformMPSTwoByTwoLinearSpan";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Geometry/delazzarimotwaniseynnaeve2022umpsspan");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The span of binary uniform matrix product states of bond dimension two has an exact parity-dependent quartic dimension.",
        H("The linear span of binary bond-two uniform matrix product states"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("uniform-mps-two-by-two-linear-span-claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("The dimension formula for every positive length"),
                StatementSource.FromAuthor(Disp(Equivalence(Local("claim"), ClaimBody()))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For each natural length n at least one, take the complex linear span of all tensors "
                        + "whose coefficient at a binary word is the trace of the corresponding ordered product "
                        + "of two complex 2 by 2 matrices. The formula asserts that its dimension is "
                        + "(n⁴ − 4n² + 192n + 192)/192 for even n and "
                        + "(n⁴ − 10n² + 192n + 201)/192 for odd n. The dimension and every occurrence "
                        + "of n in these two polynomials are cast from natural numbers to rational numbers. "
                        + "This is Conjecture 3.8 in sigma22-099.tex, lines 540–547, for positive lengths. "
                        + "The parametrization is given in lines 215–223; lines 224–225 distinguish its image "
                        + "from its closure. A finite-dimensional complex linear subspace is closed, so taking "
                        + "the span of the image gives the same span as taking the span of that closure."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("uniform-mps-two-by-two-linear-span-result"),
                DeclarationHandle.Create(Module + ".result"),
                H("The exact dimension"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "First compare the tensor span with the span of its coordinate functions. "
                            + "Let V be the space of complex functions on binary words of length n, and let S "
                            + "be the span of the trace tensors in V. Send a linear functional f on V to the "
                            + "function of a matrix pair p given by f(traceWord 2 2 n p). Expanding a tensor "
                            + "in the coordinate basis expresses this function as a linear combination of the "
                            + "trace coordinates. Conversely, each coordinate function is the image of the "
                            + "corresponding coordinate projection. Thus the image of this linear map is "
                            + "exactly the coordinate span, and its kernel is the annihilator of S. "
                            + "Rank-nullity, the dimension formula for an annihilator, and equality of the "
                            + "dimensions of V and its dual show that the tensor span and coordinate span "
                            + "have the same dimension.")),
                    Paragraph(Text(
                        "Next count the exponent vectors e with five natural entries satisfying "
                            + "e(0) + e(1) + 2e(2) + 2e(3) + 2e(4) + 4 = n. "
                            + "Each entry is at most the weighted sum, so imposing the bound e(j) < n + 1 "
                            + "does not change this count. The number of five-entry vectors with ordinary "
                            + "sum k is the cardinality of the kth symmetric power of a five-element set: "
                            + "the binomial coefficient (k + 4 choose 4), or "
                            + "(k + 1)(k + 2)(k + 3)(k + 4)/24.")),
                    Paragraph(Text(
                        "Divide the first two exponents by two and retain their residues modulo two. "
                            + "At length 2k + 5 their residues are opposite. Either choice of the first "
                            + "residue leaves a five-entry vector of ordinary sum k, giving twice "
                            + "(k + 4 choose 4). At length 2k + 6 the residues agree: the even-even case "
                            + "leaves ordinary sum k + 1, and the odd-odd case leaves ordinary sum k. "
                            + "This gives (k + 5 choose 4) + (k + 4 choose 4). The maps are inverted by "
                            + "doubling the first two entries and restoring their residues. There are no "
                            + "such exponent vectors below length four, and at length four only the zero "
                            + "vector occurs. Including these small lengths, polynomial simplification "
                            + "gives (n⁴ − 4n²)/192 exponent vectors for even n, and "
                            + "(n⁴ − 10n² + 9)/192 for odd n.")),
                    Paragraph(Text("The trace-coordinate dimension theorem "),
                        Ref("D5/S3/Quantum/TensorNetworks/UniformMPSTwoByTwoTraceWords.coordinate_dimension"),
                        Text(
                            " gives n + 1 plus exactly this exponent count. Its independent family consists "
                                + "of the n + 1 traces tr(XᵃYⁿ⁻ᵃ), together with the commutator-square invariant "
                                + "times every invariant monomial of weighted degree n − 4. Substitute that "
                                + "dimension in the equality of tensor and coordinate dimensions. Finally cast "
                                + "the natural-number sum to the rational numbers and add n + 1 to the two "
                                + "counts, obtaining the asserted even and odd formulas."))),
                DescribeRole.Theorem))));

    private static Formula ClaimBody()
    {
        Formula n = X("n");
        Formula q = CastRational(n);
        Formula fourth = new Formula.Power(q, D(4));
        Formula square = new Formula.Power(q, D(2));
        Formula linear = Multiply(D(1, 9, 2), q);
        Formula even = new Formula.Fraction(
            Add(Add(Subtract(fourth, Multiply(D(4), square)), linear), D(1, 9, 2)), D(1, 9, 2));
        Formula odd = new Formula.Fraction(
            Add(Add(Subtract(fourth, Multiply(D(1, 0), square)), linear), D(2, 0, 1)), D(1, 9, 2));
        Formula span = At(Qualified("Submodule", "span"), Complexes(),
            At(Qualified("D5", "S3", "Quantum", "TensorNetworks", "UniformMPSExpectedDimensionRefutation", "uMPS"),
                D(2), D(2), n));
        Formula vectors = Arrow(Arrow(At(Qualified("Fin"), n), At(Qualified("Fin"), D(2))), Complexes());
        Formula dimension = At(Qualified("Module", "finrank"), Complexes(),
            At(Qualified("Subtype"), LambdaOf("x", vectors,
                new Formula.Relation(X("x"), FormulaRelationOperator.MemberOf, span))));
        return All("n", Naturals(), Arrow(LE(D(1), n),
            Equal(CastRational(dimension), At(Qualified("ite"), At(Qualified("Even"), n), even, odd))));
    }

    private static Formula Local(string name) =>
        Qualified("D5", "S3", "Quantum", "TensorNetworks", "UniformMPSTwoByTwoLinearSpan", name);
    private static Formula CastRational(Formula value) =>
        Typed(At(Qualified("Nat", "cast"), value), Rationals());
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
    private static Formula Rationals() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LE(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
}
