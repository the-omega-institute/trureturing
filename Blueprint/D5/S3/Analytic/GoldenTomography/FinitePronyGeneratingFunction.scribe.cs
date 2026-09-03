using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.GoldenTomography;

internal sealed class FinitePronyGeneratingFunctionDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite Prony moment sequence has a rational generating function on its common convergence disk.",
        H("Finite Prony Generating Function"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-prony-rational-generating-function"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/GoldenTomography/FinitePronyGeneratingFunction."
                        + "finite_prony_rational_generating_function"),
                H("Finite exponential moments have the expected partial-fraction generating function"),
                StatementSource.FromAuthor(GeneratingFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a finite family of nodes and weights, assume each product of a "
                            + "node with the generating-function variable has norm below one. "
                            + "The moment power series is then summable and equals the finite "
                            + "sum of weights multiplied by the reciprocals of one minus the "
                            + "corresponding node-variable products.")),
                    Paragraph(Text(
                        "The proof applies the geometric-series theorem to each mode and "
                            + "commutes only a finite mode sum with the convergent time series. "
                            + "It supplies the exact rational-transfer layer used by Prony and "
                            + "finite Koopman methods. It asserts no meromorphic continuation, "
                            + "infinite-mode interchange, or noisy reconstruction bound."))),
                DescribeRole.Theorem)),
        []));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Sub(string name, string idx) =>
        Seq(F.Id(name), Underscore, Grp(F.Id(idx)));

    private static Formula GeneratingFormula() => Disp(Seq(
        Call("Summable", Seq(Sub("c", "n"), Cdot, Sp, F.Id("z"), Caret, Grp(F.Id("n")))),
        Sp, Land, Sp,
        Call("G", F.Id("z")), Sp, Eq, Sp,
        Sum, Underscore, Grp(F.Id("j")), Sp,
        Frac, Grp(Sub("w", "j")),
        Grp(Seq(D(1), Minus, Sub("x", "j"), Cdot, Sp, F.Id("z")))));
}
