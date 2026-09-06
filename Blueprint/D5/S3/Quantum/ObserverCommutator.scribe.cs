using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum;

internal sealed class ObserverCommutatorDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Schwinger =
        LibraryNoteRef.Create("D5/L/schwinger1960unitary");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The represented read-update commutator is the predecessor read-value difference times the predecessor amplitude.",
        H("The Observer Read-Update Commutator"),
        Blocks(
            Paragraph(Text(
                "For an arbitrary index type I, a register is a function from I "
                + "to the complex numbers. A permutation tau acts by pullback: "
                + "observerUpdate(tau,psi)(i) = psi(tau inverse(i)). The read "
                + "operator multiplies pointwise: readObservable(f,psi)(i) "
                + "= f(i) times psi(i). These are the represented operators of "),
                Ref("D5/S3/Quantum/ObserverAlgebra"), Text(".")),
            Describe.Lean(
                DescribeId.Create("observer-read-update-commutator"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/ObserverCommutator.observer_read_update_commutator_formula"),
                H("The commutator as a translated observable difference"),
                StatementSource.FromAuthor(CommutatorFormula()),
                AssessedProvenance.FromRepo(Schwinger),
                Blocks(
                    Paragraph(Text(
                        "For every permutation tau of I and every pair of "
                        + "complex-valued functions f and psi on I, the difference "
                        + "between updating after reading and reading after "
                        + "updating is the function sending i to "
                        + "(f(tau inverse(i)) - f(i)) times psi(tau inverse(i)). "
                        + "No finiteness or inhabitability hypothesis on I and "
                        + "no nonvanishing hypothesis on psi are required.")),
                    Paragraph(Text(
                        "Function extensionality reduces the equality to an "
                        + "entrywise identity. Unfolding the two operators "
                        + "produces two products with the same predecessor "
                        + "amplitude, and distributivity gives the formula. "
                        + "It determines the commutator even when it vanishes. "
                        + "Schwinger's finite unitary-operator construction is "
                        + "background for the represented read-update setting; "
                        + "the identity here is a repository derivation for an "
                        + "arbitrary index type."))),
                DescribeRole.Theorem))));

    private static Formula Parenthesized(Formula formula) => Seq(Open, formula, Close);

    private static Formula CommutatorFormula()
    {
        var predecessor = Seq(Tau, Caret, Grp(Minus, D(1)),
            Parenthesized(F.Id("i")));
        var difference = Parenthesized(Seq(
            F.Id("f"), Parenthesized(predecessor), Sp, Minus, Sp,
            F.Id("f"), Parenthesized(F.Id("i"))));

        return Disp(Seq(
            Forall, Sp, F.Id("I"), Comma, Esc,
            Forall, Sp, Tau, Sp, InMacro, Sp, Call("Perm", F.Id("I")), Comma, Esc,
            Forall, Sp, F.Id("f"), Comma, Sp, Psi, Colon,
            F.Id("I"), To, Mathbb, Grp(F.Id("C")), Comma, Esc,
            Subtract(
                Call("observerUpdate", Tau, Call("readObservable", F.Id("f"), Psi)),
                Call("readObservable", F.Id("f"), Call("observerUpdate", Tau, Psi))),
            Sp, Eq, Sp,
            Parenthesized(Seq(F.Id("i"), Sp, Mapsto, Sp,
                difference, Sp, Cdot, Sp, Psi, Parenthesized(predecessor)))));
    }
}
