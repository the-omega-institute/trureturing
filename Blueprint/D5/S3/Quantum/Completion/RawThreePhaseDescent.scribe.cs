using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Completion;

internal sealed class RawThreePhaseDescentDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/Quantum/Completion/RawThreePhaseDescent.";
    private static Formula M => F.Id("M");
    private static Formula U => F.Id("U");
    private static Formula C => F.Id("c");
    private static Formula A => F.Id("a");
    private static Formula B => F.Id("b");
    private static Formula X => F.Id("u");
    private static Formula Y => F.Id("v");
    private static Formula Z => F.Id("z");
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Add(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula Mul(Formula a, Formula b) => Seq(a, Sp, Cdot, Sp, b);
    private static Formula Mark(Formula a) => Call("U", a);
    private static Formula Third(Formula a) => Mark(Mark(Mark(a)));
    private static Formula Read(Formula a, Formula b) => Call("c", a, b);
    private static Formula All(Formula a, Formula body) =>
        Seq(Open, Forall, Sp, a, Colon, Sp, M, Comma, Sp, body, Close);
    private static Formula Law => Call("RawBalance", U, C);
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Frame(Formula body) => Seq(
        Forall, Sp, M, Colon, Sp, F.Id("Type"), Comma, Sp,
        OpenBracket, Call("MulOneClass", M), CloseBracket, Comma, Sp,
        U, Colon, Sp, Arrow(M, M), Comma, Sp,
        C, Colon, Sp, Arrow(M, Arrow(M, Seq(Mathbb, Grp(F.Id("R"))))), Comma, Sp, body);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Raw three-phase balance forces marker invariance and contextual three-step readout invariance on an arbitrary unital magma.",
        H("Raw Three-Phase Descent Prerequisite"),
        Blocks(
            Entry("raw-three-phase-balance", "RawBalance", "The original raw balance hypotheses",
                Frame(Eqn(Law, Seq(Open,
                    Eqn(Mark(D(1)), D(1)), Sp, Land, Sp,
                    All(A, All(B, Seq(D(0), Sp, Le, Sp, Read(A, B)))), Sp, Land, Sp,
                    All(A, Eqn(Read(A, A), D(0))), Sp, Land, Sp,
                    All(A, All(B, All(X, All(Y, Balance())))), Close))),
                "M has only a binary operation and a two-sided unit. U is an arbitrary self-map fixing the unit, and c is finite and real-valued. No associativity, commutativity, cancellation, inverse, marker homomorphism, surjectivity, periodicity, symmetry or positive-semidefinite form is assumed.",
                DescribeRole.Definition),
            Entry("raw-marker-readouts", "raw_marker_readouts", "The comparison has derived marker invariance",
                Frame(Seq(Law, Sp, Rightarrow, Sp,
                    Open,
                    All(X, All(Y, Eqn(Read(Mark(X), Mark(Y)), Read(X, Y)))), Sp, Land, Sp,
                    All(A, All(B, All(X, All(Y,
                        Eqn(Read(Mul(A, Third(X)), Mul(B, Third(Y))),
                            Read(Mul(A, X), Mul(B, Y))))))), Sp, Land, Sp,
                    All(X, All(Z, Seq(Open,
                        Eqn(Read(Third(X), Z), Read(X, Z)), Sp, Land, Sp,
                        Eqn(Read(Z, Third(X)), Read(Z, X)), Close))), Close)),
                "For s(n)=c(U^n u,U^n v), the raw law at the two units gives s(n+1)+s(n+2)=2s(n). Nonnegativity at every natural n rules out the growing alternating component by induction and an Archimedean contradiction. Subtracting the balance identity for (u,v) from that for (Uu,Uv) gives contextual invariance. Specializing either contextual input to the unit yields every row and column equality. Only the readings have period three; the original marker need not have period three.",
                DescribeRole.Theorem),
            Paragraph(Text("This is the Section 2 prerequisite of C133 Continuation V. The anchored free-space bilinear form, both radical pairings, zero-fibre elimination, full fibre collapse and the complete Hilbert representation criterion remain open. No physical preparation, scalar control, reference or clock follows from this result.")))));

    private static Formula Balance() => Eqn(
        Add(Add(Read(Mul(A, X), Mul(B, Y)),
            Read(Mul(A, Mark(X)), Mul(B, Mark(Y)))),
            Read(Mul(A, Mark(Mark(X))), Mul(B, Mark(Mark(Y))))),
        Add(Mul(D(3), Read(A, B)), Mul(D(3), Read(X, Y))));

    private static DocumentBlock Entry(string id, string declaration, string title,
        Formula formula, string narrative, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Gid + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(narrative))), role);
}
