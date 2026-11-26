using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.AURICOmega;

internal sealed class OmegaCircleClosureDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/AURICOmega/OmegaCircleClosure";

    public DocumentDefinition Create()
    {
        Formula p = F.Id("p"), q = F.Id("q"), k = F.Id("k"), r = F.Id("r"), s = F.Id("s");
        Formula zero = D(0), one = D(1), minusOne = Seq(Minus, D(1));
        Formula kappa = Call("kappa", p, q), spread = Call("spread", p, q);
        Formula x = Call("X", p, q), y = Call("Y", p, q);
        Formula nonzero = new Formula.Logic(Ne(p, zero), FormulaLogicOperator.Or, Ne(q, zero));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Signed projective overlap and the rational Cayley circle for Chapter 32, sections 32.7 and 32.8.",
            H("Signed projective overlap and antipodal closure"),
            Blocks(
                Law("signed-overlap-scaling", "kappa_scale", "Nonzero signed scales preserve overlap",
                    All(["p", "q", "k"], If(Ne(k, zero), Equiv(Call("kappa", Mul(k, p), Mul(k, q)), kappa))),
                    "The overlap is q squared divided by p squared plus q squared. The common scale contributes the same positive square to numerator and denominator. At the zero pair both readings are undefined and equivalent."),
                Law("overlap-spread-conservation", "kappa_add_spread_eq_one", "Overlap and spread sum to one",
                    All(["p", "q"], If(nonzero, Equiv(Add(kappa, spread), one))),
                    "Spread has numerator p squared and the same denominator as overlap. The nonzero-pair hypothesis keeps that denominator positive."),
                Law("cayley-circle-unit", "cayley_circle_unit", "The rational Cayley image has unit norm",
                    All(["p", "q"], If(nonzero, Equiv(Add(Mul(x, x), Mul(y, y)), one))),
                    "The Cayley coordinates X and Y have numerators q squared minus p squared and twice p times q, respectively. Both use the denominator p squared plus q squared. The squared norm of the numerator pair is the square of this denominator."),
                Law("cayley-antipodal-closure", "cayley_antipodal_closure", "The point at infinity maps to the antipode",
                    All(["p"], If(Ne(p, zero), And(
                        Equiv(Call("kappa", p, zero), zero), And(
                            Equiv(Call("spread", p, zero), one), And(
                                Equiv(Call("X", p, zero), minusOne),
                                Equiv(Call("Y", p, zero), zero)))))),
                    "When q vanishes and p is nonzero, the denominator is p squared. This gives overlap zero, spread one and the finite Cayley image at the antipode."),
                Law("projective-circle-product-norm", "projective_circle_mul_normSq",
                    "Homogeneous multiplication multiplies squared norms",
                    All(["p", "q", "r", "s"], new Formula.Relation(
                        Mul(Call("normSq", p, q), Call("normSq", r, s)),
                        FormulaRelationOperator.Equal, Call("normSq", Call("projectiveMul", p, q, r, s)))),
                    "Here normSq is the sum of the two coordinate squares. The product of (p,q) and (r,s) has coordinates ps+qr and qs-pr. Its mixed terms cancel in the sum of squares. The identity also holds for zero pairs."))));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula All(string[] variables, Formula body) =>
        Disp(new Formula.BindMany(FormulaQuantifier.ForAll,
            [.. variables.Select(name => new Formula.BoundVariable(
                FormulaIdentifier.Create(name), Seq(Mathbb, Grp(F.Id("Z")))))], body));

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Equiv(Formula left, Formula right) =>
        Call("Equivalent", left, right);
    private static Formula Ne(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula If(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static DocumentBlock.Describe Law(string id, string selector, string title, Formula statement, string commentary) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create($"{Module}.{selector}"),
            H(title),
            StatementSource.FromAuthor(statement),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(commentary))),
            DescribeRole.Theorem);
}
