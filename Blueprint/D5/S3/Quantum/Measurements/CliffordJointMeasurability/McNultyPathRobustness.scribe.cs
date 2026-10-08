using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurements.CliffordJointMeasurability;

internal sealed class McNultyPathRobustnessDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurements/CliffordJointMeasurability/McNultyPathRobustness.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumStates/mcnulty2025pathrobustness");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The operator certificate gives the upper bound for P₂ₙ.",
        H("McNulty Path Robustness"),
        Blocks(
            Paragraph(Text("Formulas retain Lean application and binder notation. Omega denotes the outcome-index type Ω, whereas ω denotes an outcome. Square brackets denote anonymous typeclass assumptions. Scalar coercions display their target types; angle brackets suppress the proof field of a Fin value. The identity is written as 1. Products of matrices and scalar actions use a centered dot; the operand types distinguish them. Infix Matrix.kronecker denotes the Lean kronecker notation.")),
            Node("claim", "claim", F0(),
                "McNulty, Conjecture 1, p. 9, verbatim: \"For all n ≥ 1, paths satisfy\" η(P₂ₙ) = η(P₂ₙ₊₁) = η(C₂ₙ₊₂) = (2/(2n+2)) csc(π/(2n+2)). The claim quantifies over every d and every realization on ℂ^d; Realization includes 1 ≤ d. The graph conventions are Mathlib pathGraph and cycleGraph. IsGreatest states both attainability and the upper bound in the feasible visibility subset of [0,1].", "claim",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "result", F1(),
                "The operator certificate gives the upper bound for P₂ₙ. Restricting a parent to its initial induced path gives the same upper bound for P₂ₙ₊₁ and C₂ₙ₊₂. For the lower bound, each family is represented or extended by 2n+2 Majoranas and compressed from the Fourier-vacuum parent. The even-cycle construction uses the central involution and relabels the final outcome in each central sector.", "result",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("mcnulty-2025-path-robustness"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Call(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula F0() => Disp(new Formula.Aligned([
            Seq(Call("claim"), Sp, Iff, Sp, Parenthesized(Seq(Forall, Sp, F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, Comma, Sp, D(1), Sp, Leq, Sp, F.Id("n"), Sp, To, Sp, Parenthesized(Seq(Forall, Sp, F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, Comma, Sp, Forall, Sp, F.Id("A"), Sp, Colon, Sp, Call("Fin"), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, F.Id("n"))), Sp, To, Sp, Parenthesized(Seq(Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Comma, Sp, Call("Realization"), Sp, Parenthesized(Seq(Call("SimpleGraph"), Sp, Dot, Sp, Call("pathGraph"), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, F.Id("n"))))), Sp, F.Id("A"), Sp, To, Sp, Call("IsGreatest"), Sp, Seq(OpenBrace, Seq(F.Id("eta"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Sp, Bar, Sp, F.Id("eta"), Sp, InMacro, Sp, Call("Set"), Sp, Dot, Sp, Call("Icc"), Sp, D(0), Sp, D(1), Sp, Land, Sp, Call("JM"), Sp, F.Id("A"), Sp, F.Id("eta")), CloseBrace), Sp, Parenthesized(Seq(Call("visibility"), Sp, F.Id("n"))))), Sp, Land, Sp, Parenthesized(Seq(Forall, Sp, F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, Comma, Sp, Forall, Sp, F.Id("A"), Sp, Colon, Sp, Call("Fin"), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, F.Id("n"), Sp, Plus, Sp, D(1))), Sp, To, Sp, Parenthesized(Seq(Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Comma, Sp, Call("Realization"), Sp, Parenthesized(Seq(Call("SimpleGraph"), Sp, Dot, Sp, Call("pathGraph"), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, F.Id("n"), Sp, Plus, Sp, D(1))))), Sp, F.Id("A"), Sp, To, Sp, Call("IsGreatest"), Sp, Seq(OpenBrace, Seq(F.Id("eta"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Sp, Bar, Sp, F.Id("eta"), Sp, InMacro, Sp, Call("Set"), Sp, Dot, Sp, Call("Icc"), Sp, D(0), Sp, D(1), Sp, Land, Sp, Call("JM"), Sp, F.Id("A"), Sp, F.Id("eta")), CloseBrace), Sp, Parenthesized(Seq(Call("visibility"), Sp, F.Id("n"))))), Sp, Land, Sp, Parenthesized(Seq(Forall, Sp, F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, Comma, Sp, Forall, Sp, F.Id("A"), Sp, Colon, Sp, Call("Fin"), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, F.Id("n"), Sp, Plus, Sp, D(2))), Sp, To, Sp, Parenthesized(Seq(Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Comma, Sp, Call("Realization"), Sp, Parenthesized(Seq(Call("SimpleGraph"), Sp, Dot, Sp, Call("cycleGraph"), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, F.Id("n"), Sp, Plus, Sp, D(2))))), Sp, F.Id("A"), Sp, To, Sp, Call("IsGreatest"), Sp, Seq(OpenBrace, Seq(F.Id("eta"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Sp, Bar, Sp, F.Id("eta"), Sp, InMacro, Sp, Call("Set"), Sp, Dot, Sp, Call("Icc"), Sp, D(0), Sp, D(1), Sp, Land, Sp, Call("JM"), Sp, F.Id("A"), Sp, F.Id("eta")), CloseBrace), Sp, Parenthesized(Seq(Call("visibility"), Sp, F.Id("n"))))))))
        ]));

    private static Formula F1() => Disp(new Formula.Aligned([
            Call("claim")
        ]));
}
