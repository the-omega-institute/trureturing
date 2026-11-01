using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class FourPathFeedbackRigidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite-dimensional polar-feedback rigidity step in Section 9.",
        H("Trace saturation fixes the actual feedback"),
        Blocks(Describe.Lean(
            DescribeId.Create("trace-saturation-forces-polar-feedback"),
            DeclarationHandle.Create("D5/S3/Quantum/Recovery/FourPathFeedbackRigidity.trace_saturation_forces_polar_feedback"),
            H("A single common phase for every nonzero coordinate"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Source: QUANTUM_REALITY_FOUR_PATH_FULL_RECORD_RECOVERY_BOUND, Section 9, Theorem 9.4, equations (9.22) and the first equality of (9.23). The canonical atom_id is 9f4e8ab8a85221187bed0676209bd5de7796bcad65dacfa00d3b7b0bfa8f7df5; the Lean theorem is trace_saturation_forces_polar_feedback.")),
                Paragraph(Text("For each natural n, the system index is Fin(n+1). U is an actual complex unitary matrix and v has no zero coordinate. The trace saturation hypothesis uses the sum of all coordinate moduli. The conclusion gives one complex scalar z of norm one, common to every diagonal coordinate, and sets every off-diagonal coordinate to zero. star is complex conjugation, ite is the indicated conditional, and the real norm in the denominator is cast to the complex numbers.")),
                Paragraph(Text("Put L=sum(norm(v(i))) and S=trace(U diagonal(v)). Nonzero coordinates make L positive. Construct z=S/L; saturation gives norm(z)=1. Every real part of star(z) U(i,i) v(i) is at most norm(v(i)), while their sum is L. Equality of these finite sums forces equality at every coordinate. The imaginary parts then vanish, giving star(z) U(i,i) v(i)=norm(v(i)). This both aligns the phases and forces norm(U(i,i))=1. Each unitary column has squared norm one, so all its remaining entries vanish. Multiplication by the conjugate of v(i) yields the stated polar correction.")),
                Paragraph(Text("The four-path specialization is n=3. This proves the feedback rigidity implication for a single full-support vector. It does not derive the saturation premise from a channel optimum, identify either record ray, prove the second equality with the fixed U_sigma in (9.23), or establish the support equivalence, equal sign masses, unique optimizer channel, compactification or stability. The canonical parent atom therefore remains unresolved. The existing FourPathQuadraticMajorant proves the analytic majorant and supplies neither these missing bridges nor the equality characterization."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Logic(Formula left, FormulaLogicOperator op, Formula right) =>
        new Formula.Logic(left, op, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula TheoremFormula()
    {
        Formula nat = Seq(Mathbb, Grp(F.Id("N"))), complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula n = F.Id("n"), u = F.Id("U"), v = F.Id("v"), z = F.Id("z");
        Formula i = F.Id("i"), j = F.Id("j");
        Formula size = new Formula.Binary(n, FormulaBinaryOperator.Add, Num(1));
        Formula index = Call("Fin", size), matrix = Call("Matrix", index, index, complex);
        Formula vi = Apply(v, i);
        Formula nonzero = All("i", index,
            new Formula.Relation(vi, FormulaRelationOperator.NotEqual, Num(0)));
        Formula total = Seq(new Formula.Subscript(Sum, Seq(i, Colon, index)),
            Sp, Grp(Call("norm", vi)));
        Formula saturated = Eqn(Call("norm", Call("trace", Mul(u, Call("diagonal", v)))), total);
        Formula polar = new Formula.Fraction(Mul(z, Call("star", vi)), Call("norm", vi));
        Formula conclusion = Ex("z", complex,
            Logic(Eqn(Call("norm", z), Num(1)), FormulaLogicOperator.And,
                All("i", index, All("j", index,
                    Eqn(Apply(u, i, j), Call("ite", Eqn(i, j), polar, Num(0)))))));
        Formula unitary = new Formula.Relation(u, FormulaRelationOperator.MemberOf,
            Call("unitaryGroup", index, complex));
        Formula hypotheses = Logic(unitary, FormulaLogicOperator.And,
            Logic(nonzero, FormulaLogicOperator.And, saturated));
        return Disp(All("n", nat, All("U", matrix,
            All("v", new Formula.TypeArrow(index, complex),
                Logic(hypotheses, FormulaLogicOperator.Implies, conclusion)))));
    }
}
