using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Shimura.IntegralModel;

internal sealed class GroupBaseChangeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Group Base Change", H("Group Base Change"),
        Blocks(
            Paragraph(Text("PEL datum with theta group, Lagrangian and padding; good primes; class identities. Base change of group schemes with ring action: points, sections, homomorphisms.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Shimura/IntegralModel/GroupBaseChange.exists_hom_baseChange"),
                H("exists_hom_baseChange"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let A', B' be base changes of A, B along b, c : S' → S, and F a natural map from c- to b-structures. An O-linear homomorphism χ : A → B induces one A' → B', acting on points through F and χ, compatible with pulled-back sections.")))))));
}
