using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class SignalingDimensionHellyCertificateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/QuantumChannels/SignalingDimensionHellyCertificate.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Geometry/doolittlechitambar2021certifying");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At most binomially many inputs certify that a finite classical channel requires more than d messages.",
        H("A Helly bound for classical signaling dimension"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("is-simulable"),
                DeclarationHandle.Create(Prefix + "IsSimulable"),
                H("Simulation with finite shared randomness"),
                StatementSource.FromAuthor(Disp(SimulationFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "A simulation uses a shared random index l in Fin n, a probability distribution q, "
                        + "an encoder t l from inputs to d messages, and a decoder r l from messages to k outputs. "
                        + "Each encoder and decoder is row stochastic: all its entries are nonnegative and each row sums to one. "
                        + "The channel is their composition averaged with weights q l. All sums range over the entire displayed finite type.")),
                    Paragraph(Text(
                        "This is equation (Eq:d-simulate) in arXiv:2102.12543v1, main.tex lines 150–158; "
                        + "lines 160–162 define the signaling polytope of such channels. The source writes P(y|x) "
                        + "as a column stochastic matrix; here p x y places the input first. The definition allows "
                        + "an arbitrary input type α and natural k and d, and explicitly requires finite shared randomness."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A small input set still excludes d-message simulation"),
                StatementSource.FromAuthor(Disp(ResultFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For every finite row stochastic channel p, with 1 ≤ d < k, failure of d-message simulation "
                        + "already occurs on a nonempty set i of at most binomial(k,d) inputs. The restriction keeps "
                        + "all k outputs and uses the subtype of inputs belonging to i. The hypotheses on d, k and p "
                        + "are implications in the formula. SetLike.coe makes the conversion of i from a finite set "
                        + "to a set explicit; both the cardinality and the binomial coefficient are natural numbers. "
                        + "This is the certificate-size conclusion conjectured in arXiv:2102.12543v1, main.tex line 409. "
                        + "It asserts neither sharpness of the bound nor a classification of facets.")),
                    Paragraph(Text(
                        "Let S be the type of d-element subsets s of Fin k and let K be its cardinality, binomial(k,d). "
                        + "For each input x define Fₓ to consist of vectors q on S with nonnegative coordinates summing to one "
                        + "for which there are nonnegative numbers aₛᵧ, zero when y is outside s, such that "
                        + "the sum over y of aₛᵧ is qₛ and the sum over s of aₛᵧ is p x y. Thus q is a common "
                        + "distribution on output subsets, while a describes how its mass produces the row at x.")),
                    Paragraph(Text(
                        "First, a stochastic matrix u on finite types decomposes into deterministic functions f "
                        + "with weights equal to the product over x of u x (f x). These weights are nonnegative. "
                        + "Distributing the sums over functions as a product of row sums shows that their total is one. "
                        + "The product row marginal identity shows that their weighted indicator of f x = y is u x y.")),
                    Paragraph(Text(
                        "Next, consider a finite mixture of deterministic maps v j with nonnegative weights w j summing to one, "
                        + "each map having at most d outputs. Since d < k, extend each image to a d-element subset s j. "
                        + "For each subset t, sum the weights of the indices with s j = t to obtain q t. "
                        + "For each input x and output y, sum the weights with both s j = t and v j x = y to obtain a t y. "
                        + "Nonnegativity, support, and the two sum identities show that this single q belongs to every Fₓ.")),
                    Paragraph(Text(
                        "Apply the deterministic decomposition to every encoder and decoder of a simulation. "
                        + "The mixture indices are triples (l,f,g), where f maps inputs to Fin d and g maps Fin d to Fin k. "
                        + "Give the triple weight q l times the product over x of t l x (f x), times the product over μ of r l μ (g μ). "
                        + "The associated map sends x to g(f x), so its image has at most d elements. "
                        + "The product weights sum to one; summing first over g and then over f, using the marginal identities, "
                        + "recovers the simulation equation. The preceding construction therefore gives a point in every Fₓ.")),
                    Paragraph(Text(
                        "Conversely, any mixture indexed by a finite type can be indexed by Fin of its cardinality using a bijection, "
                        + "without changing its sums. Suppose the input type is nonempty and a single q belongs to every Fₓ. "
                        + "Choose the arrays a separately for each x, and for each s choose a bijection e s from Fin d to the elements of s. "
                        + "When q s is nonzero, define the encoder c s x μ as a x s (e s μ) divided by q s. "
                        + "When q s is zero, use the point mass at z = 0 in Fin d, which exists because 1 ≤ d. "
                        + "Nonnegativity and the sum identity make c s stochastic. Use the deterministic decoder sending μ to e s μ. "
                        + "If q s is zero, every a x s y is zero because nonnegative entries sum to zero. "
                        + "If q s is nonzero, cancellation and the bijection e s show that the contribution of subset s is exactly a x s y.")),
                    Paragraph(Text(
                        "Finally decompose each c s into deterministic encoders f. The pair (s,f) receives weight "
                        + "q s times the product over x of c s x (f x), encoder f, and the same decoder for s. "
                        + "These weights are nonnegative and sum to one. Their row marginals give the contribution a x s y; "
                        + "summing over s gives p x y. Reindexing this finite mixture constructs a simulation. "
                        + "For an empty input type a simulation exists directly: take one shared index, the vacuous encoder, "
                        + "and a decoder constantly returning output zero, which exists because 1 ≤ d < k.")),
                    Paragraph(Text(
                        "Each Fₓ is convex. Given two points with arrays a and u and nonnegative coefficients b and c "
                        + "with b + c = 1, combine their distributions and arrays coordinatewise as b a + c u. "
                        + "The support and normalization equations are preserved, and the output marginal becomes "
                        + "b times p x y plus c times p x y, again p x y.")),
                    Paragraph(Text(
                        "To obtain the normalized form of Helly's theorem, consider any finite family of convex sets of vectors on "
                        + "a nonempty finite type β, all having coordinate sum one. Choose a coordinate s and delete it, "
                        + "mapping vectors linearly to the coordinates indexed by b ≠ s. This map is injective on the sum-one hyperplane: "
                        + "equality of the other coordinates and their sums forces equality at s. The target space has dimension "
                        + "cardinality(β) − 1, as the deleted-coordinate type together with one point is in bijection with β. "
                        + "If every subfamily of at most cardinality(β) sets had a common point, their linear images would satisfy "
                        + "Convex.helly_theorem'. A common image point lifts to a point in each original set; "
                        + "injectivity makes all these lifts equal. An empty total intersection therefore gives a nonempty "
                        + "subfamily of at most cardinality(β) sets with empty intersection. The empty family itself has a common zero vector.")),
                    Paragraph(Text(
                        "Now failure of simulation first implies m > 0, by the empty-input construction. "
                        + "Also K > 0 because d < k. The sets Fₓ have empty total intersection, since a common point "
                        + "would give a simulation by the converse construction. Apply the normalized Helly argument to these convex sets "
                        + "to obtain a nonempty input set i with at most K elements and empty intersection. "
                        + "If the restriction of p to i were simulable, the forward construction would give one q belonging to Fₓ "
                        + "for every x in i, contradicting that empty intersection. Substituting K = binomial(k,d) proves the bound."))),
                DescribeRole.Theorem))));

    private static Formula SimulationFormula()
    {
        Formula ql = At(X("q"), X("l"));
        Formula t = At(X("t"), X("l"));
        Formula r = At(X("r"), X("l"));
        Formula composition = SumOver("l", FinOf(X("n")), Multiply(ql,
            SumOver("μ", FinOf(X("d")), Multiply(At(r, X("μ"), X("y")), At(t, X("x"), X("μ"))))));
        Formula conditions = And(
            All("l", FinOf(X("n")), LE(Typed(D(0), Reals()), ql)),
            Equal(SumOver("l", FinOf(X("n")), ql), Typed(D(1), Reals())),
            All("l", FinOf(X("n")), Stochastic(t)),
            All("l", FinOf(X("n")), Stochastic(r)),
            All("x", X("α"), All("y", FinOf(X("k")), Equal(At(X("p"), X("x"), X("y")), composition))));
        Formula simulation = Some("n", Naturals(),
            Some("q", Arrow(FinOf(X("n")), Reals()),
                Some("t", Arrow(FinOf(X("n")), Arrow(X("α"), Arrow(FinOf(X("d")), Reals()))),
                    Some("r", Arrow(FinOf(X("n")), Arrow(FinOf(X("d")), Arrow(FinOf(X("k")), Reals()))),
                        conditions))));
        return All("α", Qualified("Type"), All("k", Naturals(), All("d", Naturals(),
            All("p", Channel(X("α")), Iff(LocalCall("IsSimulable", X("d"), X("p")), simulation)))));
    }

    private static Formula ResultFormula()
    {
        Formula set = Typed(At(Qualified("SetLike", "coe"), X("i")), At(Qualified("Set"), FinOf(X("m"))));
        Formula restriction = At(Qualified("Set", "domRestrict"), set, X("p"));
        Formula conclusion = Some("i", At(Qualified("Finset"), FinOf(X("m"))), And(
            At(Qualified("Finset", "Nonempty"), X("i")),
            LE(At(Qualified("Finset", "card"), X("i")), At(Qualified("Nat", "choose"), X("k"), X("d"))),
            Not(LocalCall("IsSimulable", X("d"), restriction))));
        return All("m", Naturals(), All("k", Naturals(), All("d", Naturals(),
            Arrow(LE(Typed(D(1), Naturals()), X("d")), Arrow(LT(X("d"), X("k")),
                All("p", Channel(FinOf(X("m"))),
                    Arrow(Stochastic(X("p")), Arrow(Not(LocalCall("IsSimulable", X("d"), X("p"))), conclusion))))))));
    }

    private static Formula Stochastic(Formula p) => At(Qualified("D5", "S3", "Estimation", "DecisionRisk",
        "DescentDefectBounds", "IsRowStochastic"), p);
    private static Formula Channel(Formula domain) => Arrow(domain, Arrow(FinOf(X("k")), Reals()));
    private static Formula LocalCall(string name, params Formula[] args) =>
        At(Qualified("D5", "S3", "Quantum", "QuantumChannels", "SignalingDimensionHellyCertificate", name), args);
    private static Formula X(string name) => name switch { "α" => Alpha, "μ" => Mu, _ => F.Id(name) };
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
    private static Formula Parenthesized(Formula value) => new Formula.LatexSequence([Open, value, Close]);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula FinOf(Formula n) => At(Qualified("Fin"), n);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(X(name), Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula LE(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula LT(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Not(Formula value) => new Formula.Not(Parenthesized(value));
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula And(params Formula[] values)
    {
        Formula result = values[^1];
        for (var index = values.Length - 2; index >= 0; index--)
            result = new Formula.Logic(Parenthesized(values[index]), FormulaLogicOperator.And, Parenthesized(result));
        return result;
    }
}
