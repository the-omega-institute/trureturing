using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds;

internal sealed class HamiltonianDisplacementDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A self-adjoint Hamiltonian bounds the angle traversed by its actual exponential evolution.",
        H("Hamiltonian displacement and centered energy fluctuation"),
        Blocks(Describe.Lean(
            DescribeId.Create("hamiltonian-displacement"),
            DeclarationHandle.Create("D5/S3/QuantumBounds/HamiltonianDisplacement.hamiltonian_displacement"),
            H("The Mandelstam–Tamm bound for every real time"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromLiterature(
                LibraryNoteRef.Create("D5/L/QuantumBounds/deffnercampbell2017speedlimits")),
            Blocks(
                Paragraph(Text("Let E be a finite-dimensional complex inner product space, A a continuous complex linear endomorphism that is self-adjoint, and psi a unit vector. The real calibration hbar is strictly positive. Define mu as the real part of inner(psi,A psi) and Delta as norm(A psi-mu psi). The theorem bounds the existing Fubini–Study angle fsAngle(psi,exp((-i t/hbar) A)psi) by abs(t) Delta/hbar for every real t. The inner product is conjugate-linear in its first argument and linear in its second. The displayed exponential is the normed-algebra exponential of the given operator.")),
                Paragraph(Text("Center A at mu and put B=A-mu I and G=(-i/hbar)B. The exponential U(s)=exp(sG) is unitary. Its vector orbit v(s)=U(s)psi has derivative w(s)=U(s)(G psi), with norm(v(s))=1 and norm(w(s))=Delta/hbar. Self-adjointness makes inner(psi,A psi) real, so inner(psi,G psi)=0. Unitary invariance of the inner product gives inner(v(s),w(s))=0 at every real s.")),
                Paragraph(Text("Regard E as a real inner product space and write r(s)=Re inner(psi,v(s)). Projection onto the real tangent plane gives norm(psi-r(s)v(s)) squared = 1-r(s) squared. Cauchy–Schwarz therefore bounds abs(r'(s)) by (Delta/hbar) sqrt(1-r(s) squared). For 0<=q<1, differentiate arccos(q r(s)). Its denominator is positive, and q sqrt(1-r(s) squared)<=sqrt(1-q squared r(s) squared) bounds the absolute derivative by Delta/hbar. The mean-value inequality on the whole real line bounds arccos(q r(t)) by arccos(q)+abs(t) Delta/hbar. Continuity as q tends to one proves the bound for arccos(r(t)), including the singular endpoints of arccos.")),
                Paragraph(Text("The commuting scalar identity term gives v(t)=exp(i t mu/hbar) exp((-i t/hbar)A)psi. This scalar phase has norm one and preserves the overlap modulus. Since the real part of a complex number is at most its modulus and arccos is decreasing, the bound for the real overlap implies the stated angle bound. No overlap modulus or energy fluctuation is divided by, so zero fluctuation, zero time, negative time, and overlaps of modulus zero or one are all retained.")),
                Paragraph(Text("This supplies an actual Hamiltonian evolution satisfying the displacement premise used by record_time_lower_bound in FubiniStudyRecordTime. For a positive resource parameter energy that bounds Delta, evaluation at a nonnegative contact duration gives that premise; two endpoint preparations still require their own Hamiltonians and fluctuation bounds in the same model. The record theorem and its sequential duration budget remain separate assumptions. No bound for open-system dynamics, arbitrary measurement protocols, unbounded operators, or a universal clock tick follows.")),
                Paragraph(Text("The displacement inequality is the classical Mandelstam–Tamm result. Deffner and Campbell, Section 2.5, equation (23) and equations (29)–(33), describe the pure-state overlap angle and the energy-variance speed bound. The centered fluctuation here is the norm of (A-mu I)psi. The finite-dimensional autonomous model makes this speed constant. The projection and regularization argument is a proof of that classical result, without a claim of research novelty."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula e = F.Id("E");
        Formula a = F.Id("A");
        Formula psi = F.Id("psi");
        Formula hbar = F.Id("hbar");
        Formula t = F.Id("t");
        Formula real = Call("Real");
        Formula complex = Call("Complex");
        Formula mu = Call("Re", Call("inner", complex, psi, Call("apply", a, psi)));
        Formula delta = Call("norm", Call("subtract", Call("apply", a, psi),
            Call("scale", Call("ofReal", mu), psi)));
        Formula coefficient = Call("divide", Call("multiply", Call("negative", Call("I")),
            Call("ofReal", t)), Call("ofReal", hbar));
        Formula evolved = Call("apply", Call("exp", Call("scale", coefficient, a)), psi);
        Formula conclusion = Rel(Call("fsAngle", psi, evolved), Le,
            Call("divide", Call("multiply", Call("abs", t), delta), hbar));
        Formula body = Rel(Conj(Call("IsSelfAdjoint", a),
            Rel(Call("norm", psi), Eq, D(1)), Rel(D(0), Lt, hbar)), Implies, conclusion);
        body = All("t", real, body);
        body = All("hbar", real, body);
        body = All("psi", e, body);
        body = All("A", Call("ContinuousLinearMap", complex, e, e), body);
        return Disp(All("E", Call("Type"), Seq(Instances(e, complex), Sp, body)));
    }

    private static Formula Instances(Formula e, Formula complex) => Seq(
        OpenBracket, Call("NormedAddCommGroup", e), CloseBracket, Sp,
        OpenBracket, Call("InnerProductSpace", complex, e), CloseBracket, Sp,
        OpenBracket, Call("FiniteDimensional", complex, e), CloseBracket);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Open, Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body, Close);
    private static Formula Rel(Formula left, Formula relation, Formula right) =>
        Seq(Open, left, Sp, relation, Sp, right, Close);
    private static Formula Conj(params Formula[] statements) =>
        statements.Aggregate((left, right) => Rel(left, Land, right));
}
