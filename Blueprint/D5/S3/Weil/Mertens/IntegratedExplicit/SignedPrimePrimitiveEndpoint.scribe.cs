using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class SignedPrimePrimitiveEndpointDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact exponential endpoint for the signed prime primitive",
        H("One-sided constant bounds from 5040"),
        Blocks(Describe.Lean(DescribeId.Create("zeta-strip-iff-signed-prime-primitive-constant-bound"),
            DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/SignedPrimePrimitiveEndpoint."
                + "zeta_strip_iff_signedPrimePrimitive_constant_bound_from_5040"),
            H("Either sign at the exact rate characterizes the strip above one half"),
            StatementSource.FromAuthor(F.Disp(Claim())),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Write Qθ(x) for the integral of (θ(u)−u)/u² over u>x. The signed "
                    + "primitive integrates Qθ(x)/√x from 5040 to exp(T). "
                    + "Each nonzero real c specifies one one-sided test.")),
                Paragraph(Text("If all zero real parts are at most b, the absolute tail estimate "
                    + "in PrimeAttainedCriticalWidth bounds |x^(1−b) Qθ(x)| by a constant C "
                    + "for all sufficiently large x. With x=exp(t), the logarithmic density is "
                    + "exp(t/2) Qθ(exp(t)). Multiplying the normalized bound by exp((b−1/2)t) "
                    + "therefore bounds the density in absolute value by C exp((b−1/2)t). "
                    + "Integrating the exponential bound and absorbing the finite initial interval "
                    + "from log(5040) gives the constant majorant for either sign.")),
                Paragraph(Text("The one-sided affine continuation criterion applies with zero "
                    + "linear coefficient when b<1. For b≥1, the zeta zero-free half-plane gives "
                    + "the asserted strip directly."))),
            DescribeRole.Theorem))));

    private static Formula Field(string name) => F.Seq(F.Mathbb, F.Grp(F.Id(name)));

    private static Formula Bind(FormulaQuantifier quantifier, string name, Formula type, Formula body) =>
        new Formula.Bind(quantifier, FormulaIdentifier.Create(name), type, body);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula Rel(Formula x, FormulaRelationOperator op, Formula y) =>
        new Formula.Relation(x, op, y);

    private static Formula Claim()
    {
        var real = Field("R");
        var complex = Field("C");
        var b = F.Id("b");
        var c = F.Id("c");
        var t = F.Id("T");
        var x = F.Id("x");
        var r = F.Id("r");
        var constant = F.Id("B");
        var half = new Formula.Fraction(F.D(1), F.D(2));
        var range = new Formula.Logic(Rel(half, FormulaRelationOperator.LessThan, b),
            FormulaLogicOperator.And, Rel(c, FormulaRelationOperator.NotEqual, F.D(0)));
        var zero = Rel(F.Seq(F.Zeta, F.Open, r, F.Close), FormulaRelationOperator.Equal, F.D(0));
        var strip = Bind(FormulaQuantifier.ForAll, "r", complex, new Formula.Logic(zero,
            FormulaLogicOperator.Implies, Rel(Call("Re", r), FormulaRelationOperator.LessThanOrEqual, b)));
        var window = F.Seq(F.Int, F.Underscore, F.Grp(F.D(5, 0, 4, 0)),
            F.Caret, F.Grp(Call("exp", t)),
            new Formula.Fraction(Call("Qtheta", x), F.Seq(F.Sqrt, F.Grp(x))),
            F.Thin, F.Id("d"), x);
        var exponential = Call("exp",
            Multiply(F.Seq(F.Open, Subtract(b, half), F.Close), t));
        var comparison = Rel(Multiply(c, window), FormulaRelationOperator.LessThanOrEqual,
            Multiply(exponential, constant));
        var eventually = Bind(FormulaQuantifier.Exists, "Y", real,
            Bind(FormulaQuantifier.ForAll, "T", real,
                new Formula.Logic(Rel(F.Id("Y"), FormulaRelationOperator.LessThanOrEqual, t),
                    FormulaLogicOperator.Implies, comparison)));
        var majorant = Bind(FormulaQuantifier.Exists, "B", real,
            new Formula.Logic(Rel(F.D(0), FormulaRelationOperator.LessThanOrEqual, constant),
                FormulaLogicOperator.And, eventually));
        var iff = new Formula.Logic(strip, FormulaLogicOperator.Iff, majorant);
        return Bind(FormulaQuantifier.ForAll, "b", real, Bind(FormulaQuantifier.ForAll, "c", real,
            new Formula.Logic(range, FormulaLogicOperator.Implies, iff)));
    }
}
