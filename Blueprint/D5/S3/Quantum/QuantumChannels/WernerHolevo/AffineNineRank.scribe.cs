using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels.WernerHolevo;

internal sealed class AffineNineRankDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/QuantumChannels/WernerHolevo/AffineNineRank";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Choi rank and decomposition of the symmetric Werner–Holevo channel.",
        H("Choi rank and decomposition of the symmetric Werner–Holevo channel"),
        Blocks(Describe.Lean(
            DescribeId.Create("symmetric-choi-rank"),
            DeclarationHandle.Create(Module + ".choiRank_symmetricWernerHolevo"),
            H("Choi rank of the symmetric channel"),
            StatementSource.FromAuthor(Disp(Seq(
                Call("rank", new Formula.Subscript(F.Id("J"), Phi)), Sp, Eq, Sp,
                new Formula.Fraction(Seq(F.Id("n"), Open, F.Id("n"), Plus, D(1), Close), D(2))))),
            AssessedProvenance.FromLiterature(
                LibraryNoteRef.Create("D5/L/QuantumChannels/girard2022mixedunitaryrank")),
            Blocks(Paragraph(DefinitionDsl.Text(
                "For a finite index type of cardinality n, the unnormalized Choi operator is 2/(n+1) times "
                + "the projection onto the symmetric subspace of the two tensor factors. Under vectorization "
                + "its range is the entire space of n by n complex symmetric matrices. The n diagonal coordinates "
                + "and one coordinate per unordered pair of distinct indices give dimension n(n+1)/2. "
                + "The Choi matrix of a single unitary conjugation has rank at most one, so every finite mixture needs at least this many terms."))),
            DescribeRole.Theorem))));
}
