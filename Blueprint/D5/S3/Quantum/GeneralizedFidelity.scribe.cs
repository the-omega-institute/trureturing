using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum;

internal sealed class GeneralizedFidelityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/GeneralizedFidelity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/rajaei2026generalized");
    private static Formula P => F.Id("P");
    private static Formula Q => F.Id("Q");
    private static Formula R => F.Id("R");
    private static Formula Phi => F.Id("Phi");
    private static Formula Root(Formula a) => Call("sqrt", a);
    private static Formula Inverse(Formula a) => Seq(a, Caret, Grp(Minus, D(1)));
    private static Formula Product(params Formula[] factors) => Seq(factors);
    private static Formula Trace(Formula a) => Call("tr", a);
    private static Formula RealPart(Formula a) => Call("Re", a);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fixed bit-flip qubit channel strictly increases the squared generalized "
        + "Bures--Wasserstein quantity throughout an explicit interval of reference states.",
        H("Qubit Generalized Fidelity and Failure of Data Processing"),
        Blocks(
            Node("fidelity", "The ordered matrix-root trace", FidelityFormula(),
                "For any finite index type n with decidable equality, R, P and Q are "
                + "actual complex n by n matrices. fidelity(R,P,Q) is the trace of "
                + "sqrt(sqrt(R) P sqrt(R)) R inverse sqrt(sqrt(R) Q sqrt(R)). "
                + "Every root is CFC.sqrt, the positive semidefinite matrix root on "
                + "positive semidefinite arguments. The source domain requires "
                + "positive-definite R and permits singular positive semidefinite P,Q. "
                + "The total definition does not assert the source's properties outside that domain.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("bures", "The full real trace quantity", BuresFormula(),
                "bures(R,P,Q) is Re tr(P+Q) minus twice Re fidelity(R,P,Q). "
                + "The trace term is retained in the definition. It equals two only "
                + "after establishing trace(P)=trace(Q)=1. On the source's Hermitian "
                + "states the trace is real, so taking its real part gives precisely "
                + "the source's squared generalized Bures--Wasserstein distance.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("rawMatrix", "The action of an actual quantum channel", RawFormula(),
                "A QuantumChannel is the existing completely positive complex linear "
                + "map on CStarMatrix with trace preservation. Complete positivity "
                + "requires positivity at every matrix amplification. rawMatrix "
                + "converts an arbitrary qubit matrix to CStarMatrix, applies the "
                + "channel, and converts the value back through ofMatrix inverse. "
                + "The star algebra equivalence transports matrix positivity in both directions.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("claim", "The unrestricted qubit assertion", ClaimFormula(),
                "For every actual complex two by two P,Q,R and every genuine "
                + "QuantumChannel from qubits to qubits, assume P,Q positive "
                + "semidefinite with trace one, R positive definite with trace one, "
                + "and the transported R positive definite. The assertion is "
                + "bures(Phi(R),Phi(P),Phi(Q)) <= bures(R,P,Q). No invertibility "
                + "condition is imposed on P or Q. This is the residual universal "
                + "qubit question explicitly retained in Rajaei's abstract and qubit discussion.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "A complete interval counterexample", Disp(new Formula.Not(F.Id("claim"))),
                "Let P=[[1,3],[3,9]]/10, Q=[[4,2],[2,1]]/5, "
                + "R=diag(1-e,e), X=[[0,1],[1,0]] and Phi(M)=31M/32+XMX/32. "
                + "For every real 0<e<=1/1000, both input states are positive "
                + "semidefinite of trace one, and both reference states are positive "
                + "definite of trace one. The two Kraus matrices sqrt(31/32)I "
                + "and sqrt(1/32)X are normalized and give the existing genuine "
                + "CPTP channel. On every complex matrix its action equals Fourier "
                + "phase damping with retention 15/16. The reference output is "
                + "diag((31-30e)/32,(1+30e)/32). Positive candidates whose squares "
                + "are the two references and the four sandwiches identify all "
                + "six actual roots by uniqueness. Expanding the ordered trace "
                + "gives F_in=(2+e)/sqrt(2(4+29e-24e^2))>7/10. "
                + "For S=sqrt(961+27900e-27900e^2), A=(95+450e+S)/640 "
                + "and B=(1955-1350e+3S)/2560, the output is "
                + "F_out=(A+B-707/1600)/(2sqrt(AB)). The bounds "
                + "31<=S<32 and S<=31+450e put A in [63/320,1/4] and "
                + "B in [3/4,4/5]. The exact rectangle certificate "
                + "(A+B-707/1600)^2-49AB/25<=-27/40000, with positive "
                + "numerator and denominators, gives F_out<7/10. "
                + "Trace-one proofs then imply B_in<3/5<B_out throughout "
                + "the interval. Instantiating e=1/1000 contradicts the universal assertion. "
                + "The conclusion has no term premises. It neither repeats the source's "
                + "higher-dimensional counterexample nor classifies all reference bases.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("generalized-fidelity-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula FidelityFormula()
    {
        var r = Root(R);
        return Equal(Call("fidelity", R, P, Q), Trace(Product(
            Root(Product(r, P, r)), Inverse(R), Root(Product(r, Q, r)))));
    }

    private static Formula BuresFormula() => Equal(Call("bures", R, P, Q), Seq(
        RealPart(Trace(Seq(P, Plus, Q))), Minus, D(2), RealPart(Call("fidelity", R, P, Q))));

    private static Formula RawFormula() => Equal(Call("rawMatrix", Phi, F.Id("M")),
        Call("ofMatrixInverse", Call("Phi", Call("ofMatrix", F.Id("M")))));

    private static Formula ClaimFormula() => Disp(Seq(
        Forall, Sp, P, Comma, Q, Comma, R, Comma, Phi, Comma, Esc,
        Call("PSD", P), Sp, Land, Sp, Call("PSD", Q), Sp, Land, Sp,
        Equal(Trace(P), D(1)), Sp, Land, Sp, Equal(Trace(Q), D(1)), Sp, Land, Sp,
        Call("PD", R), Sp, Land, Sp, Equal(Trace(R), D(1)), Sp, Land, Sp,
        Call("CPTP", Phi), Sp, Land, Sp, Call("PD", Call("rawMatrix", Phi, R)),
        Sp, Rightarrow, Sp,
        Call("bures", Call("rawMatrix", Phi, R), Call("rawMatrix", Phi, P),
            Call("rawMatrix", Phi, Q)), Sp, Le, Sp, Call("bures", R, P, Q)));
}
