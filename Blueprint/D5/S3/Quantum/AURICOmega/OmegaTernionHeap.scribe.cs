using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.AURICOmega;

internal sealed class OmegaTernionHeapDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/AURICOmega/OmegaTernionHeap";

    public DocumentDefinition Create()
    {
        Formula a = F.Id("a"), b = F.Id("b"), c = F.Id("c"), d = F.Id("d");
        Formula x = F.Id("x"), y = F.Id("y"), z = F.Id("z"), u = F.Id("u"), v = F.Id("v");
        Formula p = F.Id("p"), q = F.Id("q"), one = D(1);
        Formula integers = Seq(Mathbb, Grp(F.Id("Z")));
        Formula quaternions = F.Id("Quaternion"), spinors = F.Id("PythSpinor");
        Formula dot = Call("dot", a, b), fidelity = Call("kappa", a, b);
        Formula normProduct = Mul(Norm(a), Norm(b));
        Formula radius = Call("liftRadius", a, b, c, d);
        Formula signed = Call("kappaSpin", p, q);
        Formula affine = Sub(Mul(D(2), signed), one);
        return DocumentDefinition.Create(ScribeNode.Create(
            "Integer Hamilton quaternions, the projective ternion heap and the signed spinor kernel for Chapter 32, section 32.8 and Appendix Q.",
            H("Quaternion norms and projective ternion laws"),
            Blocks(
                Law("omega-quaternion-product-norm", "normSq_mul", "Quaternion multiplication multiplies squared norms",
                    All(quaternions, ["a", "b"], Equal(Norm(Call("mul", a, b)), normProduct)),
                    "The squared norm is the sum of the four squared integer coordinates. The identity holds for all input pairs."),
                Law("omega-ternion-left-absorption", "triad_left_absorption", "Left absorption of rays",
                    All(quaternions, ["x", "z"], If(And(Nz(x), Nz(z)), Ray(Triad(x, x, z), z))),
                    "Multiplying x by its conjugate leaves the scalar squared norm, so the repeated pair contributes a nonzero signed scale."),
                Law("omega-ternion-right-absorption", "triad_right_absorption", "Right absorption of rays",
                    All(quaternions, ["x", "z"], If(And(Nz(x), Nz(z)), Ray(Triad(x, z, z), x))),
                    "The conjugate of z followed by z gives the same central scalar squared norm."),
                Law("omega-ternion-associativity", "triad_assoc", "Nested ternion products agree as rays",
                    All(quaternions, ["x", "y", "z", "u", "v"], If(
                        And(Nz(x), And(Nz(y), And(Nz(z), And(Nz(u), Nz(v))))),
                        Ray(Triad(Triad(x, y, z), u, v), Triad(x, y, Triad(z, u, v))))),
                    "Both nestings multiply x, the conjugate of y, z, the conjugate of u and v in the same order."),
                Law("omega-ternion-lagrange", "lagrange_identity", "The four-dimensional Lagrange identity",
                    All(quaternions, ["a", "b"], Equal(Sub(normProduct, Mul(dot, dot)), Call("minorSquares", a, b))),
                    "The right side sums the squares of the six minors a_i b_j minus a_j b_i, one for each coordinate pair i < j."),
                Law("omega-ternion-fidelity-bound", "kappa_le_one", "Projective fidelity is bounded by one",
                    All(quaternions, ["a", "b"], If(And(Nz(a), Nz(b)),
                        new Formula.Relation(fidelity, FormulaRelationOperator.LessOrEqual, one))),
                    "The denominator is the product of squared norms. The Lagrange identity gives the nonnegative difference between that product and the squared dot product."),
                Law("omega-ternion-fidelity-translation", "kappa_heap_invariant", "Common heap translation preserves fidelity",
                    All(quaternions, ["a", "b", "u", "v"], If(And(Nz(u), Nz(v)),
                        Equiv(Call("kappa", Triad(a, u, v), Triad(b, u, v)), fidelity))),
                    "The common right factor is the conjugate of u times v. Its squared norm scales each squared norm and the dot product by the same positive factor."),
                Law("omega-spinor-cayley-lift", "lift_normSq", "The Cayley lift gives a rational unit spinor",
                    All(integers, ["a", "b", "c", "d"],
                        Equal(Norm(Call("liftNum", a, b, c, d)), Mul(radius, radius))),
                    "The homogeneous lift uses numerator (a²−s, 2ab, 2ac, 2ad) and radius a²+s, where s=b²+c²+d². Every nonzero quadruple gives a positive radius."),
                Law("omega-spinor-quadratic-kernel", "quadratic_kernel", "The signed kernel determines the ray kernel",
                    All(spinors, ["p", "q"], Equiv(Call("kappaProj", p, q), Mul(affine, affine))),
                    "Twice the signed fidelity minus one is the signed dot product divided by the product of the two radii. Squaring gives projective fidelity."))));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula All(Formula domain, string[] names, Formula body) =>
        Disp(new Formula.BindMany(FormulaQuantifier.ForAll,
            [.. names.Select(name => new Formula.BoundVariable(FormulaIdentifier.Create(name), domain))], body));

    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula If(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Triad(Formula x, Formula y, Formula z) => Call("triad", x, y, z);
    private static Formula Ray(Formula left, Formula right) => Call("RayEquiv", left, right);
    private static Formula Equiv(Formula left, Formula right) => Call("Equivalent", left, right);
    private static Formula Nz(Formula x) => Call("Nonzero", x);
    private static Formula Norm(Formula x) => Call("normSq", x);

    private static DocumentBlock.Describe Law(string id, string selector, string title, Formula statement, string commentary) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create($"{Module}.{selector}"), H(title),
            StatementSource.FromAuthor(statement), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(commentary))), DescribeRole.Theorem);
}
