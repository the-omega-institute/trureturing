using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class FibVajdaDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("Vajda's identity relates shifted Fibonacci products over the integers.",
H("Vajda's Fibonacci Identity"),
Blocks(
            Describe.Lean(
                DescribeId.Create("vajda-fibonacci-identity"),
                DeclarationHandle.Create("D5/S1/Recurrence/FibVajda.fib_vajda"),
                H("Vajda's identity"),
                StatementSource.FromAuthor(Disp(Seq(F.Id("F"), Underscore, Grp(F.Id("n"), Plus, F.Id("i")), F.Id("F"), Underscore, Grp(F.Id("n"), Plus, F.Id("j")), Sp, Minus, Sp, F.Id("F"), Underscore, F.Id("n"), Sp, F.Id("F"), Underscore, Grp(F.Id("n"), Plus, F.Id("i"), Plus, F.Id("j")), Sp, Eq, Sp, Open, Minus, D(1), Close, Caret, F.Id("n"), Sp, F.Id("F"), Underscore, F.Id("i"), Sp, F.Id("F"), Underscore, F.Id("j")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For natural indices n, i, and j, the difference between the two "
                    + "shifted Fibonacci products F_(n+i)F_(n+j) and F_nF_(n+i+j) equals "
                    + "(-1)^n F_iF_j. All terms are interpreted in the integers."))),
                DescribeRole.Theorem))));
}
