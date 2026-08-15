using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.NamingWindow;

internal sealed class GreenClassWindowEntropyEqualityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A naming window reaches its entropy bound exactly when every pinned coordinate law is " +
        "uniform on the full alphabet.",
        H("Equality in the Green-Class Window Entropy Bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("maximum-window-entropy-characterizes-uniform-coordinates"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/NamingWindow/GreenClassWindowEntropyEquality.shannonEntropy_windowLaw_eq_namingDim_iff_uniform"),
                H("Maximum window entropy characterizes uniform coordinates"),
                StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    F.Id("H"), Open,
                    Operatorname, Grp(F.Id("windowLaw")), Open,
                    Operatorname, Grp(F.Id("coordLaw")), Open, F.Id("mu"), Close,
                    Close, Close,
                    Sp, Eq, Sp,
                    F.Id("n"), Sp, Times, Sp,
                    Operatorname, Grp(F.Id("namingDim")), Open, F.Id("O"), Close,
                    Sp, Times, Sp, Log, Grp(D(2)), Sp, Leftrightarrow, RowBreak,
                    Forall, Sp, F.Id("i"), Sp, InMacro, Sp, F.Id("S"), Comma, Sp,
                    Operatorname, Grp(F.Id("coordLaw")), Open,
                    F.Id("mu"), Comma, Sp, F.Id("i"), Close,
                    Sp, Eq, Sp,
                    Open, F.Id("a"), Mapsto, Sp,
                    Operatorname, Grp(F.Id("card")), Open, F.Id("O"), Close,
                    Caret, Grp(Minus, D(1)), Close, Dot,
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "GreenClassWindowEntropy reduces the entropy of a finite naming window to " +
                        "the sum of its coordinate entropies and bounds each summand by log(card O). " +
                        "Equality of the finite sums forces every coordinate summand to attain that " +
                        "same upper bound.")),
                    Paragraph(Text(
                        "EntropyEquality then identifies each maximizing coordinate law with the " +
                        "uniform law on all of O. Conversely, uniformity at every coordinate makes " +
                        "every summand maximal, so additivity gives equality for the window.")),
                    Paragraph(Text(
                        "Only coordinates in S are constrained. When S is empty, both the entropy " +
                        "identity and the coordinatewise condition are vacuous, so the equivalence " +
                        "still holds without a separate exception."))),
                DescribeRole.Theorem))));
}
