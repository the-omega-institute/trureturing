using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels.WernerHolevo;

internal sealed class AffineNineAssemblyDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/QuantumChannels/WernerHolevo/AffineNineAssembly";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Symmetric unitary bases from parallel classes.",
        H("Symmetric unitary bases from parallel classes"),
        Blocks(Describe.Lean(
            DescribeId.Create("hollow-hilbert-schmidt"),
            DeclarationHandle.Create(Module + ".hollow_hs"),
            H("Hilbert–Schmidt pairing within one class"),
            StatementSource.FromAuthor(Disp(
                Seq(
                    Call("hs", new Formula.Subscript(F.Id("U"), Alpha),
                        new Formula.Subscript(F.Id("U"), Psi)),
                    Sp, Eq, Sp, new Formula.Fraction(D(1), D(4)), Sp,
                    Call("card", F.Id("G")), Sp,
                    new Formula.Subscript(DeltaLower, Seq(Alpha, Comma, Psi))))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(DefinitionDsl.Text(
                "Assume the block unitary is symmetric, hollow, and has squared entry magnitude one eighth away from the diagonal. "
                + "Use a bijection from all unordered block edges onto a finite additive group G. "
                + "For each pair of complex additive characters of G, diagonal character congruence multiplies each entry "
                + "by the character applied to the sum of its endpoint labels. "
                + "The Kronecker delta in the formula is one for equal characters and zero otherwise. "
                + "Summing over both orientations of each edge gives one fourth of the group character pairing."))),
            DescribeRole.Theorem))));
}
