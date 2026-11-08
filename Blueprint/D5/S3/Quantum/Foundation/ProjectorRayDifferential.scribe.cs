using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class ProjectorRayDifferentialDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Foundation/ProjectorRayDifferential.";

    public DocumentDefinition Create()
    {
        Formula e = F.Id("E"), psi = F.Id("p"), v = F.Id("v"), z = F.Id("z"),
            f = F.Id("f"), t = F.Id("t");
        Formula context(Formula body) => All("E", F.Id("Type"), Seq(
            OpenBracket, Call("NormedAddCommGroup", e), CloseBracket, Sp,
            OpenBracket, Call("InnerProductSpace", C, e), CloseBracket, Sp, body));
        Formula inner(Formula a, Formula b) => Call("inner", C, a, b);
        Formula speed = Call("sqrt", Sub(Sq(Norm(v)), Sq(Norm(inner(psi, v)))));
        Formula curve = Seq(R, To, e);
        Formula curveUnit = Call("Eventually", Seq(t, Mapsto, Sp,
            Eqn(Norm(Call("apply", f, t)), D(1))), Call("nhds", D(0)));
        Formula distanceQuotient = Seq(t, Mapsto, Sp, new Formula.Fraction(
            Call("fsAngle", psi, Call("apply", f, t)), Abs(t)));
        Formula statement = context(All("f", curve, All("p", e, All("v", e,
            Imp(Eqn(Norm(psi), D(1)), Imp(Eqn(Call("apply", f, D(0)), psi),
                Imp(Call("HasDerivAt", f, v, D(0)), Imp(curveUnit,
                    Call("Tendsto", distanceQuotient, Call("puncturedNhds", D(0)),
                        Call("nhds", speed))))))))));
        Formula movingProjector = Seq(t, Mapsto, Sp, Call("rankOne", C,
            Call("apply", f, t), Call("apply", f, t)));
        Formula projectorDerivative = Call("deriv", movingProjector, D(0));
        Formula projectorSpeed = Call("sqrt", Call("re", Call("trace", C, e,
            Call("comp", Call("rankOne", C, psi, psi),
                Call("comp", projectorDerivative, projectorDerivative)))));
        Formula projectorStatement = context(Seq(OpenBracket,
            Call("FiniteDimensional", C, e), CloseBracket, Sp,
            All("f", curve, All("p", e, All("v", e,
                Imp(Eqn(Norm(psi), D(1)), Imp(Eqn(Call("apply", f, D(0)), psi),
                    Imp(Call("HasDerivAt", f, v, D(0)), Imp(curveUnit,
                        Call("Tendsto", distanceQuotient, Call("puncturedNhds", D(0)),
                            Call("nhds", projectorSpeed)))))))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "The infinitesimal Fubini-Study speed follows from the original angle distance.",
            H("Ray distance and horizontal velocity"), Blocks(
                Paragraph(Text("The complex inner product is conjugate-linear in its first slot and linear in its second. The existing fsAngle is arccos of the norm of the complex inner product. The amplitude space is any complex inner product space; completeness and finite dimension are not required. Thus the result applies to the source's complex two-dimensional H_J once that representation has been connected.")),
                Item("horizontal", "Orthogonal residual of a rank-one projector",
                    context(All("p", e, All("z", e,
                        Eqn(Call("horizontal", psi, z), Sub(z,
                            Call("apply", Call("rankOne", C, psi, psi), z)))))),
                    "This uses Mathlib's actual rankOne operator, acting as inner(p,z) times p. For unit p the residual is orthogonal to the complex line through p. The definition is not a prescribed metric.", true),
                Item("fs_angle_speed", "Metric speed of a differentiable unit curve", statement,
                    "Let f(0) = p with norm(p) = 1, let f have real derivative v at zero, and require norm(f(t)) = 1 only in a neighbourhood of zero. Then fsAngle(p,f(t))/abs(t) tends, through nonzero real t, to sqrt(norm(v)^2 - norm(inner(p,v))^2). The curve may have arbitrary vertical phase velocity; the projection removes it. The zero horizontal-velocity case is included."),
                Item("fs_angle_speed_projector", "The same speed from the actual projector derivative", projectorStatement,
                    "In finite complex dimension let P = rankOne(p,p), and let D be the real derivative at zero of t mapped to rankOne(f(t),f(t)), in the normed space of continuous complex-linear operators. Under the same curve hypotheses, the limit is sqrt(Re Tr(P composed with D composed with D)). The displayed formula expands these two local abbreviations. The rankOne operators are coerced to linear maps for the trace; this does not alter their action."),
                Paragraph(Text("The derivation uses the exact identity fsAngle(p,z) = arcsin(norm(z - rankOne(p,p) z)) for unit p and z. The residual of the curve has derivative v - inner(p,v) p. Its difference quotients converge in norm. The continuous extension of arcsin(r)/r at zero has value one, which transfers this limit to the angle distance. This establishes the local distance normalization without defining the metric to equal the desired formula.")),
                Paragraph(Text("The moving-projector derivative is rankOne(p,v) + rankOne(v,p), obtained from the bounded real-bilinear rankOne map. Differentiating the local unit-norm condition gives Re inner(p,v) = 0, so D(p) is the horizontal velocity. Symmetry of D and the upstream rankOne trace formula give Tr(P D D) = norm(horizontal(p,v))^2. This identifies the diagonal real projector tensor with the speed measured by the original angle, without prescribing that speed as a definition.")),
                Paragraph(Text("This gives the infinitesimal amplitude metric in OmegaQ-020 Theorem 7.3. Relating it to the sphere tensor still requires the original sigma_z = -L_e R_z representation, its identification with rankOne on the original H_J, the actual derivative of P_n, and the sphere tangent formula Q(v,w) = (dot(v,w) + i dot(n,cross(v,w)))/4 for every unit n and both tangent vectors. The connection and global phase formula additionally require the local section differential, A = i inner(psi,dpsi), dA = -2 Im Q with the stated orientation, Stokes on suitable smooth or piecewise smooth patchwise surfaces, transition winding, solid-angle ambiguity by 4 pi, and the closed-loop result modulo 2 pi. The local distance result alone proves none of these global statements. No literature originality is claimed.")))));
    }

    private static Formula R => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula C => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Sub(Formula a, Formula b) => Seq(a, Minus, b);
    private static Formula Sq(Formula a) => new Formula.Power(a, D(2));
    private static Formula Norm(Formula a) => Seq(Vert, Sp, a, Vert);
    private static Formula Abs(Formula a) => Seq(Lvert, Sp, a, Rvert);
    private static DocumentBlock Item(string name, string title, Formula formula, string text, bool definition = false) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-')), DeclarationHandle.Create(Owner + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), definition ? DescribeRole.Definition : DescribeRole.Theorem);
}
