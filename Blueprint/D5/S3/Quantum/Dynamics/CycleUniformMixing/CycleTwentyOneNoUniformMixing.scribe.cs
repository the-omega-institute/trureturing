using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics.CycleUniformMixing;
internal sealed class CycleTwentyOneNoUniformMixingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Orbit sums, support masks and an exact integer Laurent identity exclude instantaneous uniform mixing on the cycle with twenty-one vertices.",
        H("CycleTwentyOneNoUniformMixing"), Blocks(
            Node("c21-cycletwentyonenouniformmixing-fourier-no-uniform-mixing-of-no-common-nonzero-root", "no_uniform_mixing_of_no_common_nonzero_root", Disp(Seq(Forall, Sp, Parenthesized(Seq(Call("t"), Sp, Colon, Sp, RealF())), Sp, Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Call("x0"), Sp, Call("x1"), Sp, Call("x2"), Sp, Call("x3"), Sp, Call("x4"), Sp, Call("x5"), Sp, Colon, Sp, ComplexF())), Sp, Comma, Sp, Call("x0"), Sp, Neq, Sp, D(0), Sp, To, Sp, Call("x1"), Sp, Neq, Sp, D(0), Sp, To, Sp, Call("x2"), Sp, Neq, Sp, D(0), Sp, To, Sp, Call("x3"), Sp, Neq, Sp, D(0), Sp, To, Sp, Call("x4"), Sp, Neq, Sp, D(0), Sp, To, Sp, Call("x5"), Sp, Neq, Sp, D(0), Sp, To, Sp, Call("D5.S3.Quantum.Dynamics.CycleUniformMixing.SupportMaskChecker.Ring.g1"), Sp, Call("x0"), Sp, Call("x1"), Sp, Call("x2"), Sp, Call("x3"), Sp, Call("x4"), Sp, Call("x5"), Sp, Eq, Sp, D(0), Sp, To, Sp, Call("D5.S3.Quantum.Dynamics.CycleUniformMixing.SupportMaskChecker.Ring.g2"), Sp, Call("x0"), Sp, Call("x1"), Sp, Call("x2"), Sp, Call("x3"), Sp, Call("x4"), Sp, Call("x5"), Sp, Eq, Sp, D(0), Sp, To, Sp, Call("D5.S3.Quantum.Dynamics.CycleUniformMixing.SupportMaskChecker.Ring.g3"), Sp, Call("x0"), Sp, Call("x1"), Sp, Call("x2"), Sp, Call("x3"), Sp, Call("x4"), Sp, Call("x5"), Sp, Eq, Sp, D(0), Sp, To, Sp, Call("D5.S3.Quantum.Dynamics.CycleUniformMixing.SupportMaskChecker.Ring.g4"), Sp, Call("x0"), Sp, Call("x1"), Sp, Call("x2"), Sp, Call("x3"), Sp, Call("x4"), Sp, Call("x5"), Sp, Eq, Sp, D(0), Sp, To, Sp, Call("D5.S3.Quantum.Dynamics.CycleUniformMixing.SupportMaskChecker.Ring.g5"), Sp, Call("x0"), Sp, Call("x1"), Sp, Call("x2"), Sp, Call("x3"), Sp, Call("x4"), Sp, Call("x5"), Sp, Eq, Sp, D(0), Sp, To, Sp, Call("D5.S3.Quantum.Dynamics.CycleUniformMixing.SupportMaskChecker.Ring.g6"), Sp, Call("x0"), Sp, Call("x1"), Sp, Call("x2"), Sp, Call("x3"), Sp, Call("x4"), Sp, Call("x5"), Sp, Eq, Sp, D(0), Sp, To, Sp, Call("D5.S3.Quantum.Dynamics.CycleUniformMixing.SupportMaskChecker.Ring.g7"), Sp, Call("x0"), Sp, Call("x1"), Sp, Call("x2"), Sp, Call("x3"), Sp, Call("x4"), Sp, Call("x5"), Sp, Eq, Sp, D(0), Sp, To, Sp, Call("D5.S3.Quantum.Dynamics.CycleUniformMixing.SupportMaskChecker.Ring.g8"), Sp, Call("x0"), Sp, Call("x1"), Sp, Call("x2"), Sp, Call("x3"), Sp, Call("x4"), Sp, Call("x5"), Sp, Eq, Sp, D(0), Sp, To, Sp, Call("D5.S3.Quantum.Dynamics.CycleUniformMixing.SupportMaskChecker.Ring.g9"), Sp, Call("x0"), Sp, Call("x1"), Sp, Call("x2"), Sp, Call("x3"), Sp, Call("x4"), Sp, Call("x5"), Sp, Eq, Sp, D(0), Sp, To, Sp, Call("D5.S3.Quantum.Dynamics.CycleUniformMixing.SupportMaskChecker.Ring.g10"), Sp, Call("x0"), Sp, Call("x1"), Sp, Call("x2"), Sp, Call("x3"), Sp, Call("x4"), Sp, Call("x5"), Sp, Eq, Sp, D(0), Sp, To, Sp, Call("False"))), Sp, To, Sp, Parenthesized(Seq(Neg, Sp, Parenthesized(Seq(Forall, Sp, Call("a"), Sp, Call("b"), Sp, Colon, Sp, Call("ZMod"), Sp, D(2,1), Sp, Comma, Sp, Call("Complex.normSq"), Sp, Parenthesized(Seq(Call("NormedSpace.exp"), Sp, Parenthesized(Seq(Call("SMul.smul"), Sp, Parenthesized(Parenthesized(Seq(Parenthesized(Seq(Call("t"), Sp, Colon, Sp, ComplexF())), Sp, Cdot, Sp, Call("Complex.I")))), Sp, Parenthesized(Call("D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Fourier.cycleA")))), Sp, Call("a"), Sp, Call("b"))), Sp, Eq, Sp, D(1), Sp, Slash, Sp, D(2,1))))))), "If the ten cleared phase equations have no common nonzero complex root, the Fourier correlations prevent uniform mixing on C21. The six actual exponential phases are nonzero and obey all ten equations whenever uniform mixing holds.", "D5/S3/Quantum/Dynamics/CycleUniformMixing/CycleTwentyOneNoUniformMixing.no_uniform_mixing_of_no_common_nonzero_root", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("c21-cycletwentyonenouniformmixing-claim", "claim", Disp(Seq(Call("claim"), Sp, Eq, Sp, Forall, Sp, Call("t"), Sp, Colon, Sp, RealF(), Sp, Comma, Sp, Exists, Sp, Call("u"), Sp, Call("v"), Sp, Colon, Sp, Call("ZMod"), Sp, D(2,1), Sp, Comma, Sp, Call("Complex.normSq"), Sp, Parenthesized(Seq(Call("NormedSpace.exp"), Sp, Parenthesized(Seq(Call("SMul.smul"), Sp, Parenthesized(Call("t")), Sp, Parenthesized(Parenthesized(Seq(Call("SMul.smul"), Sp, Parenthesized(Parenthesized(Seq(Minus, Sp, Call("Complex.I")))), Sp, Parenthesized(Seq(Call("Matrix.reindex"), Sp, Parenthesized(Seq(Call("ZMod.finEquiv"), Sp, D(2,1))), Sp, Dot, Sp, Call("toEquiv"), Sp, Parenthesized(Seq(Call("ZMod.finEquiv"), Sp, D(2,1))), Sp, Dot, Sp, Call("toEquiv"), Sp, Parenthesized(Seq(Parenthesized(Seq(Call("SimpleGraph.cycleGraph"), Sp, D(2,1))), Sp, Dot, Sp, Call("adjMatrix"), Sp, ComplexF()))))))))), Sp, Call("u"), Sp, Call("v"))), Sp, Neq, Sp, D(1), Sp, Slash, Sp, D(2,1))), "\"No complete cycle $C_{n}$, except for $C_{3}, C_{4}$, has the instantaneous uniform mixing property under the continuous-time quantum walk model.\" (Ahmadi–Belk–Tamon–Wendler, quant-ph/0209106v5, p. 7, Conjecture 1). The claim here is its C21 case: real time, exp(t • ((−Complex.I) • A)), and an existential pair of vertices. The adjacency is Mathlib cycleGraph(21).adjMatrix, reindexed through ZMod.finEquiv(21).", "D5/S3/Quantum/Dynamics/CycleUniformMixing/CycleTwentyOneNoUniformMixing.claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuantumChannels/ahmadi2003circulant"))),
            Node("c21-cycletwentyonenouniformmixing-result", "result", Disp(Call("claim")), "At every real time at least one entry of the transition-probability matrix of C21 differs from 1/21. Fourier correlations give ten cleared polynomial equations; the integer Laurent identity excludes a common nonzero root. This excludes C21 and is partial progress on the Ahmadi–Belk–Tamon–Wendler conjecture.", "D5/S3/Quantum/Dynamics/CycleUniformMixing/CycleTwentyOneNoUniformMixing.result", DescribeRole.Theorem, AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuantumChannels/gray2026cycle9")))), []));
    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(declaration), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Prose(prose))), role);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Inline[] Prose(string value)
    {
        var pieces = value.Split('$');
        var items = new System.Collections.Generic.List<Inline>();
        for (var i = 0; i < pieces.Length; i++)
            items.Add(i % 2 == 0 ? Text(pieces[i]) : Math(In(
                pieces[i] == "C_{n}" ? Seq(F.Id("C"), Underscore, Grp(F.Id("n"))) :
                Seq(F.Id("C"), Underscore, Grp(D(3)), Comma, Sp, F.Id("C"), Underscore, Grp(D(4))))));
        return items.ToArray();
    }
    private static Formula Call(string name) => name switch
    {
        "Complex.I" => Seq(Operatorname, Grp(Seq(F.Id("Complex"), Dot, F.Id("I")))),
        "Complex.normSq" => Seq(Operatorname, Grp(Seq(F.Id("Complex"), Dot, F.Id("normSq")))),
        "D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Fourier.cycleA" => Seq(Operatorname, Grp(Seq(F.Id("D5"), Dot, F.Id("S3"), Dot, F.Id("Quantum"), Dot, F.Id("Dynamics"), Dot, F.Id("CycleUniformMixing"), Dot, F.Id("OrbitIndexedSums"), Dot, F.Id("Fourier"), Dot, F.Id("cycleA")))),
        "D5.S3.Quantum.Dynamics.CycleUniformMixing.SupportMaskChecker.Ring.g1" => Seq(Operatorname, Grp(Seq(F.Id("D5"), Dot, F.Id("S3"), Dot, F.Id("Quantum"), Dot, F.Id("Dynamics"), Dot, F.Id("CycleUniformMixing"), Dot, F.Id("SupportMaskChecker"), Dot, F.Id("Ring"), Dot, F.Id("g1")))),
        "D5.S3.Quantum.Dynamics.CycleUniformMixing.SupportMaskChecker.Ring.g10" => Seq(Operatorname, Grp(Seq(F.Id("D5"), Dot, F.Id("S3"), Dot, F.Id("Quantum"), Dot, F.Id("Dynamics"), Dot, F.Id("CycleUniformMixing"), Dot, F.Id("SupportMaskChecker"), Dot, F.Id("Ring"), Dot, F.Id("g10")))),
        "D5.S3.Quantum.Dynamics.CycleUniformMixing.SupportMaskChecker.Ring.g2" => Seq(Operatorname, Grp(Seq(F.Id("D5"), Dot, F.Id("S3"), Dot, F.Id("Quantum"), Dot, F.Id("Dynamics"), Dot, F.Id("CycleUniformMixing"), Dot, F.Id("SupportMaskChecker"), Dot, F.Id("Ring"), Dot, F.Id("g2")))),
        "D5.S3.Quantum.Dynamics.CycleUniformMixing.SupportMaskChecker.Ring.g3" => Seq(Operatorname, Grp(Seq(F.Id("D5"), Dot, F.Id("S3"), Dot, F.Id("Quantum"), Dot, F.Id("Dynamics"), Dot, F.Id("CycleUniformMixing"), Dot, F.Id("SupportMaskChecker"), Dot, F.Id("Ring"), Dot, F.Id("g3")))),
        "D5.S3.Quantum.Dynamics.CycleUniformMixing.SupportMaskChecker.Ring.g4" => Seq(Operatorname, Grp(Seq(F.Id("D5"), Dot, F.Id("S3"), Dot, F.Id("Quantum"), Dot, F.Id("Dynamics"), Dot, F.Id("CycleUniformMixing"), Dot, F.Id("SupportMaskChecker"), Dot, F.Id("Ring"), Dot, F.Id("g4")))),
        "D5.S3.Quantum.Dynamics.CycleUniformMixing.SupportMaskChecker.Ring.g5" => Seq(Operatorname, Grp(Seq(F.Id("D5"), Dot, F.Id("S3"), Dot, F.Id("Quantum"), Dot, F.Id("Dynamics"), Dot, F.Id("CycleUniformMixing"), Dot, F.Id("SupportMaskChecker"), Dot, F.Id("Ring"), Dot, F.Id("g5")))),
        "D5.S3.Quantum.Dynamics.CycleUniformMixing.SupportMaskChecker.Ring.g6" => Seq(Operatorname, Grp(Seq(F.Id("D5"), Dot, F.Id("S3"), Dot, F.Id("Quantum"), Dot, F.Id("Dynamics"), Dot, F.Id("CycleUniformMixing"), Dot, F.Id("SupportMaskChecker"), Dot, F.Id("Ring"), Dot, F.Id("g6")))),
        "D5.S3.Quantum.Dynamics.CycleUniformMixing.SupportMaskChecker.Ring.g7" => Seq(Operatorname, Grp(Seq(F.Id("D5"), Dot, F.Id("S3"), Dot, F.Id("Quantum"), Dot, F.Id("Dynamics"), Dot, F.Id("CycleUniformMixing"), Dot, F.Id("SupportMaskChecker"), Dot, F.Id("Ring"), Dot, F.Id("g7")))),
        "D5.S3.Quantum.Dynamics.CycleUniformMixing.SupportMaskChecker.Ring.g8" => Seq(Operatorname, Grp(Seq(F.Id("D5"), Dot, F.Id("S3"), Dot, F.Id("Quantum"), Dot, F.Id("Dynamics"), Dot, F.Id("CycleUniformMixing"), Dot, F.Id("SupportMaskChecker"), Dot, F.Id("Ring"), Dot, F.Id("g8")))),
        "D5.S3.Quantum.Dynamics.CycleUniformMixing.SupportMaskChecker.Ring.g9" => Seq(Operatorname, Grp(Seq(F.Id("D5"), Dot, F.Id("S3"), Dot, F.Id("Quantum"), Dot, F.Id("Dynamics"), Dot, F.Id("CycleUniformMixing"), Dot, F.Id("SupportMaskChecker"), Dot, F.Id("Ring"), Dot, F.Id("g9")))),
        "False" => Seq(Operatorname, Grp(Seq(F.Id("False")))),
        "Matrix.reindex" => Seq(Operatorname, Grp(Seq(F.Id("Matrix"), Dot, F.Id("reindex")))),
        "NormedSpace.exp" => Seq(Operatorname, Grp(Seq(F.Id("NormedSpace"), Dot, F.Id("exp")))),
        "SMul.smul" => Seq(Operatorname, Grp(Seq(F.Id("SMul"), Dot, F.Id("smul")))),
        "SimpleGraph.cycleGraph" => Seq(Operatorname, Grp(Seq(F.Id("SimpleGraph"), Dot, F.Id("cycleGraph")))),
        "ZMod" => Seq(Operatorname, Grp(Seq(F.Id("ZMod")))),
        "ZMod.finEquiv" => Seq(Operatorname, Grp(Seq(F.Id("ZMod"), Dot, F.Id("finEquiv")))),
        "a" => Seq(Operatorname, Grp(Seq(F.Id("a")))),
        "adjMatrix" => Seq(Operatorname, Grp(Seq(F.Id("adjMatrix")))),
        "b" => Seq(Operatorname, Grp(Seq(F.Id("b")))),
        "claim" => Seq(Operatorname, Grp(Seq(F.Id("claim")))),
        "t" => Seq(Operatorname, Grp(Seq(F.Id("t")))),
        "toEquiv" => Seq(Operatorname, Grp(Seq(F.Id("toEquiv")))),
        "u" => Seq(Operatorname, Grp(Seq(F.Id("u")))),
        "v" => Seq(Operatorname, Grp(Seq(F.Id("v")))),
        "x0" => Seq(Operatorname, Grp(Seq(F.Id("x0")))),
        "x1" => Seq(Operatorname, Grp(Seq(F.Id("x1")))),
        "x2" => Seq(Operatorname, Grp(Seq(F.Id("x2")))),
        "x3" => Seq(Operatorname, Grp(Seq(F.Id("x3")))),
        "x4" => Seq(Operatorname, Grp(Seq(F.Id("x4")))),
        "x5" => Seq(Operatorname, Grp(Seq(F.Id("x5")))),
        _ => throw new System.ArgumentException("Unknown Lean constant", nameof(name)),
    };

    private static Formula RealF() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula ComplexF() => Seq(Mathbb, Grp(F.Id("C")));
}
