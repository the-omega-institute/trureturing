using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Depth.ContinuedFractions;

internal sealed class GaussInverseStepDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A Gauss history coordinate recovers the partial quotient that produced it.",
        H("Gauss Inverse Step"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gauss-inverse-step-recovers-quotient"),
                DeclarationHandle.Create(
                    "D5/S1/Depth/ContinuedFractions/GaussInverseStep."
                    + "gauss_inverse_step_recovers_quotient"),
                H("The inverse history step recovers its quotient"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("a"), InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma,
                    Sp, F.Id("y"), InMacro, Sp, OpenBracket, D(0), Comma, D(1), Close,
                    Comma, Sp, Lfloor, Sp, Frac, Grp(D(1)),
                    Grp(Frac, Grp(D(1)), Grp(Open, F.Id("a"), Plus, F.Id("y"), Close)),
                    Sp, Rfloor, Sp, Eq, Sp, F.Id("a")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a history coordinate y in the half-open unit interval, updating it "
                    + "to 1/(a+y) stores the partial quotient a: the integer floor of the "
                    + "reciprocal of the updated coordinate is exactly a. The proof combines "
                    + "Mathlib's involution of inversion with its floor law for an integer plus "
                    + "a value in [0,1). Only this inverse-step formula is asserted; no claim is "
                    + "made here about invertibility of the full natural extension, its invariant "
                    + "measure, or restart dynamics."))),
                DescribeRole.Theorem))));
}
