using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.WorldModel;

internal sealed class CompletionTowerDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/WorldModel/CompletionTower.CompletionTower.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fixed base state generates a unique coherent fixed thread through a completion tower.",
        H("Completion Tower and Truth Thread"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fixed-base-generates-truth-thread"),
                DeclarationHandle.Create(
                    Prefix + "transport_from_fixed_base_is_truth"),
                H("A fixed base state generates a truth thread"),
                StatementSource.FromAuthor(TruthFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A completion tower contains one typed dynamical world at every finite "
                            + "level and a semiconjugate bonding map between adjacent levels.")),
                    Paragraph(Text(
                        "A thread is coherent when each bonding map carries one coordinate to "
                            + "the next. It is a truth thread when every coordinate is also fixed "
                            + "by its local dynamics.")),
                    Paragraph(Text(
                        "Semiconjugacy propagates fixedness upward, while recursion makes the "
                            + "transported thread coherent and determined by its base coordinate."))),
                DescribeRole.Theorem))));

    private static Formula TruthFormula() => Disp(Seq(
        Call("IsFixedPt", Sub(F.Id("F"), D(0)), F.Id("x0")),
        Sp, Rightarrow, Sp,
        Call("IsTruthThread", Call("transportFromBase", F.Id("x0")))));
}
