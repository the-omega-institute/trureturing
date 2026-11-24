using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.AURICOmega;

internal sealed class OmegaShadowBridgeDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/AURICOmega/OmegaShadowBridge";

    public DocumentDefinition Create()
    {
        Formula a = F.Id("a"), b = F.Id("b"), c = F.Id("c"), d = F.Id("d");
        Formula x = F.Id("x"), y = F.Id("y"), p = F.Id("p"), q = F.Id("q");
        Formula nat = F.Id("OmegaNat"), integer = F.Id("OmegaInt"), ratio = F.Id("IntRatio");
        Formula ax = Call("fraction", a, b), cy = Call("fraction", c, d);
        Formula nonzero = Call("Nonzero", p, q);
        Formula realX = Call("toReal", Call("X", p, q)), realY = Call("toReal", Call("Y", p, q));
        Formula overlap = Call("toReal", Call("kappa", p, q));
        return DocumentDefinition.Create(ScribeNode.Create(
            "The one-way Layer 2 shadow of Omega arithmetic and its projective circle in Mathlib.",
            H("Exact transport to standard numbers"),
            Blocks(
                Definition("toStdNat", "Natural-number shadow",
                    "The zero constructor maps to zero, and a successor maps to the standard successor."),
                Definition("toStdInt", "Integer shadow",
                    "Maps each nonnegative or negative-successor constructor to its standard counterpart."),
                Definition("toRat", "Rational shadow",
                    "A finite ratio maps to its signed numerator divided by its positive denominator. The undefined constructor maps to zero."),
                Definition("toReal", "Real shadow",
                    "The rational shadow followed by the canonical inclusion of the rationals in the reals."),
                Law("toStdNat_add", "Transport of natural addition",
                    BinaryLaw("toStdNat", Add, a, b, nat), "Induction on the right argument transports successors."),
                Law("toStdNat_mul", "Transport of natural multiplication",
                    BinaryLaw("toStdNat", Mul, a, b, nat), "Induction on the right argument uses transport of natural addition."),
                Law("toStdInt_add", "Transport of integer addition",
                    BinaryLaw("toStdInt", Add, a, b, integer), "Mixed signs use transport of subtraction of two naturals."),
                Law("toStdInt_neg", "Transport of integer negation",
                    All(Equal(Call("toStdInt", Negate(a)), Negate(Call("toStdInt", a))), ("a", integer)),
                    "Negation exchanges the two sign branches except at zero."),
                Law("toStdInt_mul", "Transport of integer multiplication",
                    BinaryLaw("toStdInt", Mul, a, b, integer), "The sign cases use transport of natural multiplication."),
                Law("toRat_equivalent", "Equivalent fractions have equal rational shadows",
                    All(If(Call("Equivalent", x, y), Equal(Call("toRat", x), Call("toRat", y))),
                        ("x", ratio), ("y", ratio)),
                    "For finite fractions, equality of cross products gives equality of rational readings."),
                Law("toRat_add", "Transport of finite-ratio addition",
                    All(Equal(Call("toRat", Add(ax, cy)), Add(Call("toRat", ax), Call("toRat", cy))),
                        ("a", integer), ("c", integer), ("b", nat), ("d", nat)),
                    "The denominator predecessors encode positive denominators. The addition uses their product as a common denominator."),
                Law("toRat_mul", "Transport of ratio multiplication",
                    BinaryLaw("toRat", Mul, x, y, ratio), "Finite products multiply numerators and denominators. Undefined inputs give zero in the rational shadow."),
                Law("toRat_inv", "Transport of the reciprocal",
                    All(Equal(Call("toRat", Call("inv", x)), Call("inv", Call("toRat", x))), ("x", ratio)),
                    "A nonzero finite ratio exchanges the magnitudes with the sign in the numerator. The inverse of zero has shadow zero."),
                Law("cayley_circle_unit", "The real Cayley image has unit norm",
                    All(If(nonzero, Equal(Add(new Formula.Power(realX, D(2)), new Formula.Power(realY, D(2))), D(1))),
                        ("p", integer), ("q", integer)),
                    "The nonzero pair has positive squared norm. Its strict circle identity transports first to the rationals and then to the reals."),
                Law("kappa_unit_interval", "The real overlap is between zero and one",
                    All(If(nonzero, And(Le(D(0), overlap), Le(overlap, D(1)))), ("p", integer), ("q", integer)),
                    "Positive denominators transport both signed cross-product inequalities into the rational order, which the real inclusion preserves."))));
    }

    private static Formula BinaryLaw(string bridge, Func<Formula, Formula, Formula> op,
        Formula a, Formula b, Formula domain) =>
        All(Equal(Call(bridge, op(a, b)), op(Call(bridge, a), Call(bridge, b))),
            (((Formula.LatexWord)a).Value.Value, domain), (((Formula.LatexWord)b).Value.Value, domain));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula All(Formula body, params (string Name, Formula Domain)[] variables) =>
        Disp(new Formula.BindMany(FormulaQuantifier.ForAll,
            [.. variables.Select(variable => new Formula.BoundVariable(
                FormulaIdentifier.Create(variable.Name), variable.Domain))], body));

    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Negate(Formula a) => Seq(Minus, a);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula If(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);

    private static DocumentBlock.Describe Definition(string selector, string title, string note) =>
        Describe.Lean(DescribeId.Create(selector.ToLowerInvariant()), DeclarationHandle.Create($"{Module}.{selector}"),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(note))), DescribeRole.Definition);

    private static DocumentBlock.Describe Law(string selector, string title, Formula statement, string note) =>
        Describe.Lean(DescribeId.Create(selector.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create($"{Module}.{selector}"), H(title), StatementSource.FromAuthor(statement),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(note))), DescribeRole.Theorem);
}
