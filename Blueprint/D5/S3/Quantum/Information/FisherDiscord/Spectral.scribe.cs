using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.FisherDiscord;

internal sealed class SpectralDocument : IScribeDocumentDefinition
{
    private static DocumentBlock.Describe Item(string name, string title, string body,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create("fisher-discord-spectral-" + name.ToLowerInvariant().Replace("_", "-")),
            DeclarationHandle.Create("D5/S3/Quantum/Information/FisherDiscord/Spectral." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(body))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Spectral formulas for Fisher discord in every finite dimension.",
        H("Fisher discord and the spectrum"), Blocks(
            Item("pairKernel", "Spectral pair kernel", "The kernel is twice sqrt(ab) times the squared difference of sqrt(a) and sqrt(b), divided by a+b. Real division assigns zero to a zero denominator.", DescribeRole.Definition),
            Item("fisherSLD_diag", "Diagonal Fisher formula", "For any nonnegative real diagonal and every Hermitian SLD solution, Fisher information is one half of the sum over ordered pairs of (a-b)^2/(a+b) times the squared modulus of the observable entry. The SLD may be arbitrary on the joint zero eigenspace; the trace weights erase that freedom."),
            Item("skewWY_diag", "Diagonal skew formula", "For a nonnegative diagonal and a Hermitian observable, skew information is one half of the sum over ordered pairs of the squared difference of square roots times the squared modulus of the observable entry."),
            Item("discord_diag", "Diagonal discord formula", "Subtracting skew information from Fisher information gives one half of the sum of the pair kernel times the squared modulus of each observable entry. All SLD solutions have this same value."),
            Item("pairKernel_nonneg", "Nonnegative pair kernel", "The pair kernel is nonnegative for all nonnegative arguments, including the boundary where either or both arguments vanish."),
            Item("discord_nonneg_diag", "Nonnegative diagonal discord", "The spectral terms are nonnegative for every nonnegative diagonal, Hermitian observable and Hermitian SLD solution."),
            Item("fisherSLD_spectral", "Fisher formula in an eigenbasis", "The diagonal formula applies to every positive semidefinite matrix after conjugation by its eigenvector unitary. The observable entries are taken in that eigenbasis, and the formula holds for every Hermitian SLD solution."),
            Item("skewWY_spectral", "Skew formula in an eigenbasis", "The positive square root and skew information respect unitary conjugation. The diagonal skew formula therefore applies to the eigenvalues of every positive semidefinite matrix."),
            Item("discord_spectral", "Discord formula in an eigenbasis", "In an eigenbasis of an arbitrary positive semidefinite matrix, Fisher discord is one half of the sum of the nonnegative pair kernel times squared observable entries. No choice of SLD changes this value."),
            Item("discord_nonneg", "Nonnegative Fisher discord", "For every finite positive semidefinite matrix and Hermitian observable, Fisher information minus skew information is nonnegative for every Hermitian SLD solution."))));
}
