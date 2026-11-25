using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Conventions.IntegerIndexBinomial;

internal sealed class NativeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The executable binomial coefficient accepts an integer lower index.",
        H("Integer lower indices in executable sums"),
        Blocks(Describe.Lean(
            DescribeId.Create("executable-integer-lower-binomial"),
            DeclarationHandle.Create("D5/S0/Conventions/IntegerIndexBinomial/Native.binom_std"),
            H("The native binomial coefficient"),
            StatementSource.FromAuthor(Disp(Seq(
                F.Id("B"), Open, F.Id("m"), Comma, F.Id("j"), Close, Sp, Eq, Sp,
                F.Id("if"), Sp, F.Id("j"), Sp, Lt, Sp, D(0), Sp, F.Id("then"), Sp, D(0),
                Sp, F.Id("else"), Sp, Operatorname, Grp(F.Id("choose")), Open, F.Id("m"), Comma, F.Id("j"), Close))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "For a negative lower index the function returns zero. For a nonnegative index it "
                + "computes Mathlib’s natural binomial coefficient and returns its integer value. "
                + "The executable ballot coefficient subtracts the values at two adjacent integer indices."))),
            DescribeRole.Definition))));
}
