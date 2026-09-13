using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class PrimeSquareDoubleRootObstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/PrimeSquareDoubleRootObstruction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(
        ScribeNode.Create(
            "The unchanged quadratic factor proposed in arXiv:2603.25343v1 section 4.3 "
                + "cannot survive modulo the square. A derivative obstruction proves "
                + "the failure uniformly for every integer modulus parameter above one.",
            H("Unchanged Double-Root Lift Obstruction"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("prime-square-double-root-refutation"),
                    DeclarationHandle.Create(Prefix + "unchanged_double_root_not_dvd"),
                    H("The repeated factor is obstructed at first derivative order"),
                    StatementSource.FromAuthor(Obstruction()),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "For every natural n>1, the coefficient ring is ZMod(n^2). "
                                + "If (X-1)^2 divided X^n-1, formal differentiation and "
                                + "evaluation at 1 would force n=0 in that ring. "
                                + "This contradicts n^2 not dividing n.")),
                        Paragraph(Text(
                            "conjectured_quadratic_not_dvd identifies the polynomial "
                                + "X^2-2X+1 named by coefficients a=-2,b=1 with this "
                                + "excluded square. Section 4.3 explicitly conjectures "
                                + "these unchanged coefficients. The paper states that "
                                + "the coefficient conjecture is not required for its "
                                + "subsequent argument.")),
                        Paragraph(Text(
                            "Only that literal coefficient conjecture is refuted here. "
                                + "No general impossibility of all quadratic lifts, no "
                                + "refutation of all results of the cited paper, and no "
                                + "resolution of Wall-Sun-Sun prime existence is claimed."))),
                    DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] xs)
    {
        var result = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < xs.Length; ++i)
        {
            if (i > 0) { result.Add(Comma); result.Add(Sp); }
            result.Add(xs[i]);
        }
        result.Add(Close);
        return Seq([.. result]);
    }

    private static Formula Obstruction() => Disp(Call("NotDivides",
        Call("square", Call("sub", F.Id("X"), F.Id("1"))),
        Call("sub", Call("power", F.Id("X"), F.Id("n")), F.Id("1"))));
}
