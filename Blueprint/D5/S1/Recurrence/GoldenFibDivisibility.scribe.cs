using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class GoldenFibDivisibilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("Fibonacci divisibility detects divisibility of indices from index three onward.",
H("Fibonacci Divisibility and Indices"),
Blocks(
            Describe.Lean(
                DescribeId.Create("fibonacci-divisibility-detects-index-divisibility"),
                DeclarationHandle.Create("D5/S1/Recurrence/GoldenFibDivisibility.fib_dvd_iff"),
                H("Fibonacci divisibility detects index divisibility"),
                StatementSource.FromAuthor(Disp(Seq(F.Id("a"), Sp, Ge, Sp, D(3), Sp, Implies, Sp, Left, Open, F.Id("F"), Underscore, F.Id("a"), Sp, Mid, Sp, F.Id("F"), Underscore, F.Id("b"), Sp, Iff, Sp, F.Id("a"), Sp, Mid, Sp, F.Id("b"), Right, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For natural indices a and b with a at least three, the Fibonacci "
                    + "number F_a divides F_b exactly when a divides b. The lower bound "
                    + "removes the exceptional index two, where F_2 equals one."))),
                DescribeRole.Theorem))));
}
