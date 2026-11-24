using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.AURICOmega;

internal sealed class OmegaLieTripleAndFreeGroupDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/AURICOmega/OmegaLieTripleAndFreeGroup";

    public DocumentDefinition Create()
    {
        Formula x = F.Id("x"), y = F.Id("y"), u = F.Id("u"), v = F.Id("v"), w = F.Id("w");
        Formula a = F.Id("a"), b = F.Id("b");
        Formula vectors = F.Id("Vec3"), rationalVectors = F.Id("RatVec3"), words = F.Id("Word");
        Formula gram = Call("gramAreaSq", u, v);
        Formula rationalGram = Call("rationalGramAreaSq", u, v);
        Formula triple = Triple(u, v, w);
        Formula derivation = Triple(x, y, triple);
        Formula first = Triple(Triple(x, y, u), v, w);
        Formula second = Triple(u, Triple(x, y, v), w);
        Formula third = Triple(u, v, Triple(x, y, w));
        Formula primary = Call("denomPlus", a, b), shadow = Call("denomMinus", a, b);
        Formula half = Call("value", D(1), D(2));
        Formula output = Call("output", a, b);
        Formula radius = Call("radius", Call("product", a, b));
        Formula nonemptyReduced = And(Ne(w, F.Id("nil")), Call("IsReduced", w));
        Formula quat = Call("evalQuat", w);
        Formula AgreeOn(string axis)
        {
            Formula input = Call("ofInt", F.Id(axis));
            return Call("Equiv", Call("Ad", Call("evalQuat", u), input),
                Call("Ad", Call("evalQuat", v), input));
        }
        return DocumentDefinition.Create(ScribeNode.Create(
            "Lie triple curvature, rational dual charts, and the norm-five word theorem for Omega Math sections 4.2, 5.2, and 14.3–14.4.",
            H("Lie triple curvature, dual charts, and reduced words"),
            Blocks(
                Law("omega-lie-triple-antisymm", "lieTriple_antisymm", "The triple bracket is antisymmetric",
                    All(vectors, ["u", "v", "w"], Equal(triple, Call("neg", Triple(v, u, w)))),
                    "The bracket is dot(u,w) times v minus dot(v,w) times u."),
                Law("omega-lie-triple-jacobi", "lieTriple_jacobi", "The cyclic sum vanishes",
                    All(vectors, ["u", "v", "w"], Equal(
                        Add(Add(triple, Triple(v, w, u)), Triple(w, u, v)), F.Id("zero"))),
                    "The three terms cancel by symmetry of the dot product."),
                Law("omega-lie-triple-derivation", "lieTriple_derivation", "A fixed pair acts by a derivation",
                    All(vectors, ["x", "y", "u", "v", "w"], Equal(derivation, Add(Add(first, second), third))),
                    "The strict integer polynomial checker verifies the derivation identity in all three coordinates."),
                Law("omega-lie-triple-curvature", "lieTriple_unit_sectional_curvature", "The positive curvature numerator is the squared Gram area",
                    All(vectors, ["u", "v"], Equal(Call("dot", Triple(u, v, u), v), gram)),
                    "The Gram area is dot(u,u) times dot(v,v) minus the square of dot(u,v)."),
                Law("omega-lie-triple-curvature-reversed", "lieTriple_sectional_curvature_reversed", "The reversed contraction is the negative squared Gram area",
                    All(vectors, ["u", "v"], Equal(Call("dot", Triple(u, v, v), u), Call("neg", gram))),
                    "This identifies the sign of the contraction in the bracket convention used here."),
                Law("omega-lie-triple-curvature-ratio", "lieTriple_sectional_ratio", "Every nondegenerate rational plane has curvature one",
                    All(rationalVectors, ["u", "v"], If(Ne(Call("gramAreaSq", Call("num", u), Call("num", v)), D(0)),
                        Equiv(Call("mul", Call("rationalCurvatureNumerator", u, v), Call("inv", rationalGram)), D(1)))),
                    "Both contractions have the square of the product of the two positive vector denominators as their denominator."),
                Law("omega-dual-chart-sum", "dual_chart_denom_sum_one", "The two chart denominators sum to one",
                    All(rationalVectors, ["a", "b"], Equiv(Add(primary, shadow), D(1))),
                    "For a quaternion product with homogeneous scalar coordinate w and positive radius r, the two normalized denominators are (r+w)/(2r) and (r−w)/(2r)."),
                Law("omega-dual-chart-half", "dual_chart_denom_ge_half", "One chart denominator is at least one half",
                    All(rationalVectors, ["a", "b"], Or(Le(half, primary), Le(half, shadow))),
                    "The sign of the scalar coordinate specifies which denominator reaches the bound."),
                Law("omega-dual-chart-ball", "dual_chart_ball_containment", "The selected chart stays in the closed unit ball",
                    All(rationalVectors, ["a", "b"], Le(Call("dot", output, output), D(1))),
                    "Choose the antipodal representative with nonnegative scalar coordinate. Its stereographic output has positive denominator r+|w|."),
                Law("omega-dual-chart-mrp", "dual_chart_mrp_denominators", "The chart denominators have the expanded MRP forms",
                    All(rationalVectors, ["a", "b"], And(
                        Equiv(primary, Call("value", Call("mrpPlusNum", a, b), radius)),
                        Equiv(shadow, Call("value", Call("mrpMinusNum", a, b), radius)))),
                    "For squared input norms A, B and dot product C, the normalized numerators are 1+AB−2C and A+B+2C. Both share denominator (1+A)(1+B)."),
                Law("omega-hurwitz-word-split", "reduced_word_split5_nonzero", "A reduced word has nonzero split image",
                    All(words, ["w"], If(Call("IsReduced", w), Equal(Call("isZero", Call("evalSplit5", w)), F.Id("false")))),
                    "Each edge between adjacent outer products contributes a nonzero scalar modulo five."),
                Law("omega-hurwitz-word-norm", "reduced_word_normSq", "The squared norm is five to the word length",
                    All(words, ["w"], Equal(Call("normSq", quat), Call("powFive", Call("length", w)))),
                    "Hamilton multiplication multiplies squared norms, and every generator has squared norm five."),
                Law("omega-hurwitz-word-divisibility", "reduced_word_not_div_five", "A reduced word is primitive at five",
                    All(words, ["w"], If(Call("IsReduced", w), new Formula.Not(Call("AllDivisibleByFive", quat)))),
                    "If five divided every quaternion coordinate, the split matrix modulo five would vanish."),
                Law("omega-hurwitz-word-scalar", "reduced_word_non_scalar", "A nonempty reduced word evaluates to a nonscalar quaternion",
                    All(words, ["w"], If(nonemptyReduced, new Formula.Not(Call("IsScalar", quat)))),
                    "A scalar quaternion with squared norm a positive power of five has scalar coordinate divisible by five."),
                Law("omega-hurwitz-adjoint-injective", "reduced_words_adjoint_injective", "Distinct reduced words give distinct rational adjoint rotations",
                    All(words, ["u", "v"], If(And(Call("IsReduced", u), Call("IsReduced", v)),
                        If(And(AgreeOn("axisX"), AgreeOn("axisY")), Equal(u, v)))),
                    "Equality of the actions makes the relative quaternion scalar. Remove the common prefix, then reverse the first suffix and replace each letter by its opposite before appending the second suffix. If the original words differed, the result is nonempty and reduced."))));
    }

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula Triple(Formula u, Formula v, Formula w) => Call("lieTriple", u, v, w);
    private static Formula Equiv(Formula a, Formula b) => Call("Equivalent", a, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula If(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);

    private static Formula All(Formula domain, string[] names, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [.. names.Select(name => new Formula.BoundVariable(FormulaIdentifier.Create(name), domain))], body);

    private static DocumentBlock.Describe Law(
        string id, string selector, string title, Formula statement, string explanation) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create($"{Module}.{selector}"), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))), DescribeRole.Theorem);
}
