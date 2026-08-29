using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class GoldenEigenpairResidualDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S1/Recurrence/Invariants/GoldenEigenpairResidual."
            + "golden_eigenpair_and_fibonacci_residual";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Forward-shift iteration exposes both golden coordinates and the exact Fibonacci "
            + "contracting residual.",
        H("Golden Eigenpair and Fibonacci Residual"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-eigenpair-and-fibonacci-residual"),
            DeclarationHandle.Create(Declaration),
            H("The shifted weight has two golden faces"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The source pair is constructed by iterating the canonical forward shift "
                        + "on the two frozen golden eigensequences and evaluating both at index "
                        + "zero. Induction applies the frozen one-step eigenvector laws, so the "
                        + "two coordinates are the displayed powers.")),
                Paragraph(Text(
                    "The second conjunct directly applies the frozen Fibonacci residual theorem. "
                        + "Subtracting the expanding multiple of the current weight from the next "
                        + "weight leaves the contracting golden coordinate exactly.")),
                Paragraph(Text(
                    "No new sequence or weight is defined by the target equation; the public "
                        + "objects are the existing shift, eigensequences, and Fibonacci weight."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula k = F.Id("k");
        Formula shift = F.Id("shift");
        Formula expanding = F.Id("expandingSequence");
        Formula contracting = F.Id("contractingSequence");
        Formula weight = F.Id("fibonacciWeight");
        Formula next = Seq(k, Plus, D(1));
        Formula expandingAtZero = Apply(Call("iterate", shift, k, expanding), D(0));
        Formula contractingAtZero = Apply(Call("iterate", shift, k, contracting), D(0));
        Formula expandingPower = Seq(Varphi, Caret, Grp(next));
        Formula contractingPower = Seq(Psi, Caret, Grp(next));

        Formula pairClause = Seq(
            Langle, expandingAtZero, Comma, Sp, contractingAtZero, Rangle,
            Sp, Eq, Sp,
            Langle, expandingPower, Comma, Sp, contractingPower, Rangle);
        Formula residualClause = Seq(
            Apply(weight, next), Sp, Minus, Sp, Varphi, Sp, Cdot, Sp,
            Apply(weight, k), Sp, Eq, Sp, contractingPower);

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, Typed(k, natural), Comma),
            Seq(Open, pairClause, Close, Sp, Land),
            Seq(Open, residualClause, Close, Dot),
        ]));
    }

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);
}
