using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class CalibratedUnitaryGroupDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An operator-norm differentiable unitary group determines a Hamiltonian after independent calibration.",
        H("Calibrated unitary groups"),
        Blocks(Describe.Lean(DescribeId.Create("calibrated-group"),
            DeclarationHandle.Create("D5/S3/Quantum/Dynamics/CalibratedUnitaryGroup.calibrated_group"),
            H("The generator determines the exponential evolution"),
            StatementSource.FromAuthor(Presentation()),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Observer/giovannetti2015time")),
            Blocks(
                Paragraph(Text("Let H be a complete complex inner product space. Let U(t) be a continuous complex linear operator for each real t, with U(0)=I, U(s+t)=U(s)U(t), and U(t)*U(t)=I for every t. Assume the operator-valued map has real derivative G at zero in the operator norm. These assumptions include the original finite-dimensional differentiable unitary group, since finite-dimensional complex inner product spaces are complete. They do not assume a Hamiltonian or its equation of motion.")),
                Paragraph(Text("The group law writes U(s)=U(s-t)U(t). Differentiating at s=t proves U'(t)=G U(t) for every real t. Differentiating U(t)*U(t)=I at zero gives G*+G=0. The derivative of F(t)=exp(-tG)U(t) is therefore zero, and the mean-value constancy theorem gives F(t)=F(0)=I. Multiplying by exp(tG), whose product with exp(-tG) is I by the commuting exponential identity, proves U(t)=exp(tG). These steps construct the generator relation and the exponential representation from the original assumptions.")),
                Paragraph(Text("For an independently supplied nonzero real hbar, define Hamiltonian=i hbar G. Skew adjointness of G makes Hamiltonian self-adjoint. Scalar normalization gives U(t)=exp((-i t/hbar) Hamiltonian) and U'(t)=(-i/hbar) Hamiltonian U(t). Applying the continuous evaluation map at any initial vector psi gives the Schrodinger equation for U(t)psi; the evaluation is an exact compiled application, not another retained theorem. The original finite history, clock conditioning and all-input restoration applications remain in FinitePropagationHistory. Neither a continuous time parameter nor hbar follows from discrete gate count, and this theorem makes no claim about an unbounded generator of a merely strongly continuous group.")),
                Paragraph(Text("Giovannetti, Lloyd and Maccone discuss conditional-clock dynamics. The bounded, norm-differentiable generator argument here is a formal reuse and synthesis of standard differentiation, adjoint and exponential results, not a literature novelty claim."))),
            DescribeRole.Theorem))));

    private static Formula Presentation()
    {
        Formula space = F.Id("H");
        Formula op = Call("ContinuousComplexLinearEnd", space);
        Formula u = F.Id("U");
        Formula g = F.Id("G");
        Formula real = Call("Real");
        Formula ham = Call("calibratedHamiltonian", F.Id("hbar"), g);
        Formula premises = Conj(
            Rel(Call("apply", u, D(0)), Eq, Call("Identity", space)),
            All("s", real, All("t", real,
                Rel(Call("apply", u, Call("add", F.Id("s"), F.Id("t"))), Eq,
                    Call("compose", Call("apply", u, F.Id("s")), Call("apply", u, F.Id("t")))))),
            All("t", real, Rel(Call("compose", Call("adjoint", Call("apply", u, F.Id("t"))),
                Call("apply", u, F.Id("t"))), Eq, Call("Identity", space))),
            Call("HasDerivAt", u, g, D(0)));
        return Disp(All("H", Call("CompleteComplexInnerProductSpace"),
            All("U", Call("Map", real, op), All("G", op,
                Rel(premises, Implies, All("hbar", real,
                    Rel(Rel(F.Id("hbar"), Neq, D(0)), Implies, Conj(
                        Call("IsSelfAdjoint", ham),
                        All("t", real, Rel(Call("apply", u, F.Id("t")), Eq,
                            Call("exp", Call("scale", Call("negativeITOverHbar", F.Id("t"), F.Id("hbar")), ham)))),
                        All("t", real, Call("HasDerivAt", u,
                            Call("scale", Call("negativeIOverHbar", F.Id("hbar")),
                                Call("compose", ham, Call("apply", u, F.Id("t")))), F.Id("t")))))))))));
    }
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Open, Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body, Close);
    private static Formula Rel(Formula left, Formula relation, Formula right) =>
        Seq(Open, left, Sp, relation, Sp, right, Close);
    private static Formula Conj(params Formula[] statements) =>
        statements.Aggregate((left, right) => Rel(left, Land, right));
}
