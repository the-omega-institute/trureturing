using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurements;

internal sealed class RelevantSpaceQuantumKacDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Projection monitoring preserves the Kraus word reachable space of a Hermitian initial matrix.",
        H("The Actual Relevant Space under Projection Monitoring"),
        Blocks(
            Paragraph(Text("For a finite complex coordinate carrier n and a finite Kraus index set A, "
                + "write C(K,P) for the span of all original Kraus words applied to the support of P, "
                + "including the empty word. The support is the orthogonal complement of the kernel. "
                + "For Hermitian P it equals the range of P.")),
            Describe.Lean(
                DescribeId.Create("quantum-kac-monitored-reachable-space"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurements/RelevantSpaceQuantumKac."
                    + "monitored_reachable_space_eq"),
                H("Monitoring does not change the reachable space"),
                StatementSource.FromAuthor(ReachabilityFormula()),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Quantum/sinkovicz2014quantizedrecurrence")),
                Blocks(
                    Paragraph(Text("Each monitored branch is (I-P)K_a. The original and monitored "
                        + "branches differ by P K_a x, a vector in the initial support. Both spaces "
                        + "contain that support and are invariant under their generating branches. "
                        + "Induction on Kraus words therefore gives both inclusions.")),
                    Paragraph(Text("When P is the projection onto a unit initial vector, these are "
                        + "the actual unread no-return branches of the monitored channel, and this "
                        + "is Appendix A equation (A9). No unitality or trace-preservation assumption "
                        + "is needed for this space identity. For general Hermitian P the identity "
                        + "is algebraic and does not assert that the branches form a physical instrument.")),
                    Paragraph(Text("In the pure-state CPTP setting, the quantum Kac theorem further "
                        + "relates the sum of the actual no-return states to the orthogonal projection "
                        + "onto this common space. Its dimension is the relevant dimension; the "
                        + "space identity by itself is not a convergence or recurrence statement."))),
                DescribeRole.Theorem))));

    private static Formula ReachabilityFormula()
    {
        Formula n = F.Id("n"), a = F.Id("A"), k = F.Id("K"), p = F.Id("P");
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula matrix = Call("Matrix", n, n, complex);
        Formula branches = Seq(F.Id("a"), Sp, Mapsto, Sp,
            Open, F.Id("I"), Minus, p, Close, Sp, Call("K", F.Id("a")));
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, n, Comma, Sp, a, Colon, Sp, F.Id("Type"), Comma),
            Seq(OpenBracket, Call("Fintype", n), CloseBracket, Sp,
                OpenBracket, Call("DecidableEq", n), CloseBracket, Sp,
                OpenBracket, Call("Fintype", a), CloseBracket, Comma),
            Seq(Forall, Sp, k, Colon, Sp, a, Sp, To, Sp, matrix, Comma, Sp,
                Forall, Sp, p, Colon, Sp, matrix, Comma),
            Seq(Call("IsHermitian", p), Sp, Rightarrow, Sp,
                Call("reachableSpace", branches, p), Sp, Eq, Sp,
                Call("reachableSpace", k, p))
        ]));
    }

    private static Formula Call(string name, params Formula[] args) =>
        Seq(Operatorname, Grp(F.Id(name)), Open, Join(Seq(Comma, Sp), args), Close);
}
