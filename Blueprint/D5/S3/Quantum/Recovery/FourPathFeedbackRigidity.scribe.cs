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
                Paragraph(Text("The finite core uses the trace-saturation implication from (9.22) through the first equality of (9.23); the Lean theorem is trace_saturation_forces_polar_feedback.")),
                Paragraph(Text("For each natural n, the system index is Fin(n+1). U is an actual complex unitary matrix and v has no zero coordinate. The trace saturation hypothesis uses the sum of all coordinate moduli. The conclusion gives one complex scalar z of norm one, common to every diagonal coordinate, and sets every off-diagonal coordinate to zero. star is complex conjugation, ite is the indicated conditional, and the real norm in the denominator is cast to the complex numbers.")),
                Paragraph(Text("Put L=sum(norm(v(i))) and S=trace(U diagonal(v)). Reuse Complex.exists_norm_eq_mul_self to choose a unit scalar alpha with norm(S)=alpha*S, and set z=star(alpha). Saturation gives star(z)*S=L. Every real part of star(z) U(i,i) v(i) is at most norm(v(i)), while their sum is L. Equality of these finite sums forces equality at every coordinate. The imaginary parts then vanish, giving star(z) U(i,i) v(i)=norm(v(i)). This both aligns the phases and forces norm(U(i,i))=1. Each unitary column has squared norm one, so all its remaining entries vanish. Multiplication by the conjugate of v(i) yields the stated polar correction.")),
                Paragraph(Text("The four-path specialization is n=3. Coverage is limited to the child atom's finite core from (9.22) through the first equality of (9.23): the feedback rigidity implication for a single vector under the stated full-support and trace-saturation hypotheses. This theorem does not establish the child's full premises or ray/context, derive the saturation premise from a channel optimum, identify either record ray, prove the second equality with the fixed U_sigma in (9.23), or establish the support equivalence, equal sign masses, unique optimizer channel, compactification or stability. Neither the complete child claim nor the complete parent theorem is covered. The existing FourPathQuadraticMajorant proves the analytic majorant and supplies neither these missing bridges nor the equality characterization."))),
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
