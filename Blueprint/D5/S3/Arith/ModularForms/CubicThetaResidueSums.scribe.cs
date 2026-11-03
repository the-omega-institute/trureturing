using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.ModularForms;

internal sealed class CubicThetaResidueSumsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/ModularForms/CubicThetaResidueSums.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Fourier/huang2025signpatterns");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The three full scalar residue sums at a cubic root are zero, Euler, and Euler.", H("CubicThetaResidueSums"), Blocks(
            Paragraph(Text("The three full scalar residue sums at a cubic root are zero, Euler, and Euler.")),
            Node("0", "residueTerm", "The complete signed monomial for an integer Jacobi index in a specified cubic residue.", DescribeRole.Definition),
            Node("1", "residue_exponent_one", "The first residue exponent is precisely the generalized pentagonal number.", DescribeRole.Theorem),
            Node("2", "residue_exponent_two", "The second residue exponent is the pentagonal number of the negative integer index.", DescribeRole.Theorem),
            Node("3", "residue_exponent_reflection", "The zero-residue exponent is preserved by the integer involution m to 1-m.", DescribeRole.Theorem),
            Node("4", "hasSum_residue_zero", "The zero-residue sum vanishes by a complete integer involution, including both zero exponents.", DescribeRole.Theorem),
            Node("5", "hasSum_residue_one", "The first residue is exactly Euler's actual pentagonal series.", DescribeRole.Theorem),
            Node("6", "hasSum_residue_two", "The second residue is the same Euler series by integer negation.", DescribeRole.Theorem),
            Paragraph(Text("These are attributed classical intermediate identities. CubicThetaIdentities proves the downstream Borwein relations and EtaSignK6 proves the exact all-index sign theorem. Independent formal acceptance and publication remain separate. No priority or unique claim is made."))
        ), []));
    private static DocumentBlock Node(string id, string declaration, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("cubic-theta-residue-sums-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(declaration), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(text))), role);
}
