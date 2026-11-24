using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.AURICOmega;

internal sealed class OmegaCayleyRotationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/AURICOmega/OmegaCayleyRotation";

    public DocumentDefinition Create()
    {
        Formula p = F.Id("p"), q = F.Id("q"), k = F.Id("k"), s = F.Id("s");
        Formula a = F.Id("a"), b = F.Id("b"), u = F.Id("u"), v = F.Id("v"), n = F.Id("n");
        Formula one = D(1);
        Formula ints = Seq(Mathbb, Grp(F.Id("Z"))), naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula quaternions = F.Id("Quaternion"), vectors = F.Id("RatVec3"), spinors = F.Id("PythSpinor");
        Formula rotation = Call("Cayley", s);
        Formula step = Call("cayleyIterate", s, v, n);
        return DocumentDefinition.Create(ScribeNode.Create(
            "Exact rational three-dimensional rotations and the quaternion heap recurrence for Chapter 32, sections 32.7 and 32.8 and Appendix Q.",
            H("Adjoint and Cayley rotations"),
            Blocks(
                Law("omega-adjoint-dot", "ad_dot", "The adjoint action preserves dot products",
                    All(quaternions, ["p"], All(vectors, ["u", "v"], If(Nz(p),
                        Equiv(Dot(Ad(p, u), Ad(p, v)), Dot(u, v))))),
                    "The action sends v to the imaginary coordinates of p times the pure quaternion v times the conjugate of p, divided by the squared norm of p."),
                Law("omega-adjoint-scale", "ad_scale", "A signed quaternion scale leaves the adjoint action unchanged",
                    All(quaternions, ["p"], All(ints, ["k"], All(vectors, ["v"],
                        If(And(Nz(p), Ne(k, D(0))), Equiv(Ad(Call("scale", k, p), v), Ad(p, v)))))),
                    "The signed scale contributes its square to the numerator and the denominator."),
                Law("omega-adjoint-composition", "ad_hom", "Quaternion multiplication composes adjoint rotations",
                    All(quaternions, ["p", "q"], All(vectors, ["v"], If(And(Nz(p), Nz(q)),
                        Equiv(Ad(Call("mul", p, q), v), Ad(p, Ad(q, v)))))),
                    "The conjugate reverses the product order and the squared norm of the product multiplies the denominators."),
                Law("omega-cayley-forward", "cayley_identity", "The Cayley matrix satisfies the forward equation",
                    All(vectors, ["s"], Equiv(Call("mul", Call("skewMinus", s), rotation), Call("skewPlus", s))),
                    "The two skew factors are I−X and I+X, where X is the cross-product matrix of the rational parameter s. The equality is checked after clearing positive denominators."),
                Law("omega-cayley-orthogonal", "cayley_orthogonal", "The Cayley matrix is orthogonal",
                    All(vectors, ["s"], Equiv(Call("mul", Call("transpose", rotation), rotation), F.Id("I"))),
                    "The integer numerator has orthogonal columns with squared lengths equal to the square of the common denominator."),
                Law("omega-cayley-determinant", "cayley_det", "The Cayley matrix has determinant one",
                    All(vectors, ["s"], Equiv(Call("det", rotation), one)),
                    "The determinant of the integer numerator is the cube of the positive denominator."),
                Law("omega-cayley-iterate-norm", "cayley_iterate_norm", "Repeated Cayley steps preserve squared norm",
                    All(vectors, ["s", "v"], All(naturals, ["n"], Equiv(Dot(step, step), Dot(v, v)))),
                    "At each natural-number beat the same rational Cayley matrix acts once. The dot-product law applies at every beat."),
                Law("omega-spinor-heap-recurrence", "heap_norm_preserved", "The signed quaternion heap recurrence stays on the unit sphere",
                    All(spinors, ["a", "b"], All(naturals, ["n"],
                        Equiv(Call("spinorNormSq", Call("heapAt", a, b, n)), one))),
                    "The sequence starts at a and b. The next element is the current element times the conjugate of the previous element times the current element. The squared norm is taken after dividing by the positive spinor radius."))));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula All(Formula domain, string[] names, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [.. names.Select(name => new Formula.BoundVariable(FormulaIdentifier.Create(name), domain))], body);

    private static Formula Ne(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula If(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Nz(Formula x) => Call("Nonzero", x);
    private static Formula Ad(Formula p, Formula v) => Call("Ad", p, v);
    private static Formula Dot(Formula left, Formula right) => Call("dot", left, right);
    private static Formula Equiv(Formula left, Formula right) => Call("Equivalent", left, right);

    private static DocumentBlock.Describe Law(string id, string selector, string title, Formula statement, string commentary) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create($"{Module}.{selector}"), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(commentary))), DescribeRole.Theorem);
}
