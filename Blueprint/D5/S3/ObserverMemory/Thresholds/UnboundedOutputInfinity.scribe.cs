using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Thresholds;

internal sealed class UnboundedOutputInfinityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An unbounded natural-valued output forces its carrier to be infinite.",
        H("Unbounded Output Infinity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unbounded-output-forces-an-infinite-carrier"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Thresholds/UnboundedOutputInfinity."
                    + "unbounded_output_implies_infinite"),
                H("Unbounded output forces an infinite carrier"),
                StatementSource.FromAuthor(UnboundedOutputFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let alpha be any carrier and let f assign a natural-number output to "
                            + "each object. If every natural bound is strictly exceeded by some "
                            + "output, then alpha is infinite.")),
                    Paragraph(Text(
                        "If alpha were finite, Mathlib's Finite.bddAbove_range would supply an "
                            + "upper bound for the range of f. Applying the hypothesis to that "
                            + "bound gives an immediate contradiction.")),
                    Paragraph(Text(
                        "This closes only the unbounded-output-implies-infinite-object clause of "
                            + "the source atom. Its entropy, quantum-tax, zeta, and continued-"
                            + "fraction assertions are not claimed here."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula UnboundedOutputFormula() =>
        Disp(Seq(
            Forall, Sp, Alpha, Comma, Sp,
            F.Id("f"), Colon, Sp, Alpha, Sp, To, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
            Open, Forall, Sp, F.Id("B"), Colon, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            Exists, Sp, F.Id("x"), Colon, Sp, Alpha, Comma, Sp,
            F.Id("B"), Sp, Lt, Sp, Apply(F.Id("f"), F.Id("x")), Close, Sp,
            Rightarrow, Sp, Operatorname, Grp(F.Id("Infinite")), Open, Alpha, Close, Dot));
}
