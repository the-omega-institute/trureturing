using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CharacterSums;

internal sealed class NonprincipalCharacterGrowthDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/CharacterSums/NonprincipalCharacterGrowth.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Half-totient growth of a nonprincipal Dirichlet L-function",
        H("Cancellation within one period"),
        Blocks(
            Paragraph(Text("For a complex nonprincipal character of positive modulus q, each full "
                + "period sums to zero. Its total absolute mass is the number of units modulo q. "
                + "An incomplete period and its complement have opposite sums, so the norm of "
                + "either sum is at most half that mass.")),
            Describe.Lean(DescribeId.Create("right-half-plane"), DeclarationHandle.Create(Module + "nonprincipal_growth"),
                H("Growth throughout the right half-plane"),
                StatementSource.FromAuthor(F.Disp(new Formula.Relation(
                    Call("abs", Call("L", F.Id("s"), F.Id("chi"))), FormulaRelationOperator.LessThanOrEqual,
                    F.Seq(Call("phi", F.Id("q")), F.Sp, Call("abs", F.Id("s")), F.Slash,
                        F.Open, F.D(2), F.Sp, Call("Re", F.Id("s")), F.Close)))),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Take any complex s with σ = Re(s) > 0. Write A(t) for the character "
                        + "sum over positive integers up to t. Partial summation on σ > 1 identifies "
                        + "L(s,χ) with s times the integral of A(t)t to the power −s−1 from one to infinity. "
                        + "Boundedness of A makes its Mellin integral holomorphic throughout σ > 0, "
                        + "so analytic continuation extends the identity to this half-plane.")),
                    Paragraph(Text("The absolute value of the remaining power integrates to 1/σ. "
                        + "Multiplying by |s| and the incomplete-period bound φ(q)/2 gives the stated estimate."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
}
