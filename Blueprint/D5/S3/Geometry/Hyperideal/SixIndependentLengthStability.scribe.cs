using System;
using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class SixIndependentLengthStabilityDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Geometry/Hyperideal/SixIndependentLengthStability.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Quantitative Cauchy stability for the six-independent-length determinant remainder.",
        H("A quantitative stability envelope for broken pairing symmetry"),
        Blocks(
            Paragraph(Text(
                "For the six-independent-length character coordinates, let t be the "
                + "squared Euclidean size of the two asymmetry coordinates. Let C be "
                + "the center coefficient obtained by adding ro-1 to the Euclidean "
                + "norm of (A squared minus B squared, r minus o).")),
            Describe.Lean(
                DescribeId.Create("six-independent-asymmetry-envelope"),
                DeclarationHandle.Create(Prefix + "asymmetry_remainder_le_envelope"),
                H("The asymmetry remainder has a quadratic-plus-quartic envelope"),
                StatementSource.FromAuthor(F.Disp(EnvelopeStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The quadratic part of Xi is bounded by 2 C t through the "
                    + "two-dimensional Cauchy inequality, while the quartic part is "
                    + "at most t squared. This is the new estimate that controls both "
                    + "independent symmetry-breaking directions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("six-independent-determinant-stability"),
                DeclarationHandle.Create(Prefix + "determinant_negative_of_stability_bound"),
                H("The stability envelope forces a negative determinant"),
                StatementSource.FromAuthor(F.Disp(DeterminantStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Whenever the envelope t squared plus 2 C t is strictly below "
                    + "the product L M, the exact determinant remainder identity gives "
                    + "a negative Gram determinant. The implication only uses that "
                    + "strict bound; positive-length and geometric realization "
                    + "conditions remain separate hypotheses of the surrounding model."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("six-independent-stability-radius"),
                DeclarationHandle.Create(Prefix + "stability_bound_iff_radius"),
                H("The strict envelope is equivalent to a square-root radius"),
                StatementSource.FromAuthor(F.Disp(RadiusStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "When L and M are positive and C is positive, the strict "
                    + "quadratic-plus-quartic bound is equivalent to t being below "
                    + "sqrt(C squared plus L M) minus C. This is a sufficient radius "
                    + "for the six-length determinant criterion, not a claim that the "
                    + "radius is a maximal geometric ball."))),
                DescribeRole.Theorem))));

    private static Formula EnvelopeStatement()
    {
        var vars = Variables();
        var r = F.Id("r"); var o = F.Id("o"); var A = F.Id("A");
        var B = F.Id("B"); var xi = F.Id("xi"); var zeta = F.Id("zeta");
        var t = Call("asymmetrySize", xi, zeta);
        return All(vars, Le(Call("Xi", r, o, A, B, xi, zeta),
            Add(Pow(t, 2), Mul(Mul(F.D(2), Call("stabilityCoefficient", r, o, A, B)), t))));
    }

    private static Formula DeterminantStatement()
    {
        var vars = Variables();
        var r = F.Id("r"); var o = F.Id("o"); var A = F.Id("A");
        var B = F.Id("B"); var xi = F.Id("xi"); var zeta = F.Id("zeta");
        var t = Call("asymmetrySize", xi, zeta);
        var bound = Lt(Add(Pow(t, 2), Mul(Mul(F.D(2),
            Call("stabilityCoefficient", r, o, A, B)), t)),
            Mul(Call("L", r, o, A, B), Call("M", r, o, A, B)));
        return All(vars, Imp(bound,
            Lt(Call("det", Call("gram", r, o, A, B, xi, zeta)), F.D(0))));
    }

    private static Formula RadiusStatement()
    {
        var vars = Variables();
        var r = F.Id("r"); var o = F.Id("o"); var A = F.Id("A");
        var B = F.Id("B"); var xi = F.Id("xi"); var zeta = F.Id("zeta");
        var t = Call("asymmetrySize", xi, zeta);
        var C = Call("stabilityCoefficient", r, o, A, B);
        var envelope = Lt(Add(Pow(t, 2), Mul(Mul(F.D(2), C), t)),
            Mul(Call("L", r, o, A, B), Call("M", r, o, A, B)));
        return All(vars,
            Imp(Lt(F.D(0), Call("L", r, o, A, B)),
                Imp(Lt(F.D(0), Call("M", r, o, A, B)),
                    Imp(Lt(F.D(0), C),
                        Iff(Lt(t, Call("stabilityRadius", r, o, A, B)), envelope)))));
    }

    private static (string Name, Formula Type)[] Variables() =>
        new[] { "r", "o", "A", "B", "xi", "zeta" }
            .Select(name => (name, (Formula)F.Id("Real"))).ToArray();

    private static Formula All((string Name, Formula Type)[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [.. variables.Select(v => new Formula.BoundVariable(
                FormulaIdentifier.Create(v.Name), v.Type))], body);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
    private static Formula Add(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Mul(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Pow(Formula x, int n) =>
        new Formula.Power(x, F.D((byte)n));
    private static Formula Lt(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Le(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Imp(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Iff(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.Iff, y);
}
