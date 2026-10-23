using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class HeadleyExtensionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/FiniteGroups/HeadleyExtension.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A kernel R-cycle is spliced through an even quotient R-star cycle without choosing a group splitting.",
        H("Headley nonsplit extension splice"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("headley-extension-orthomorphism-inverse"),
                DeclarationHandle.Create(Owner + "orthomorphism_inverse"),
                H("Inverse orthomorphisms preserve the difference inventory"),
                StatementSource.FromAuthor(Disp(F.Id("orthomorphism"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If f and h ↦ f(h)-h are permutations of a finite additive abelian group, "
                    + "then h ↦ f⁻¹(h)-h is also a permutation. The proof uses the inverse "
                    + "orthomorphism pair and negates the original difference inventory."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("headley-extension-representative-system"),
                DeclarationHandle.Create(Owner + "RepresentativeSystem"),
                H("Nonsplit representatives are set-theoretic"),
                StatementSource.FromAuthor(Disp(F.Id("representatives"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A representative section of E → E/N chooses one point in each coset. "
                    + "It is not an additive section: all row coordinates are transported "
                    + "through the ambient additive group."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("headley-extension-seam-labels"),
                DeclarationHandle.Create(Owner + "splice_seam_labels"),
                H("The four exceptional seams retain their ambient labels"),
                StatementSource.FromAuthor(Disp(F.Id("seams"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "With B=A+C, F(h)=h-D(h), and a selected nonzero row v, replacing the "
                    + "two A→B→C rows by the kernel path and the short B-column path preserves "
                    + "the four labels exactly in E, including the closing edge."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("headley-extension-certificate-assembly"),
                DeclarationHandle.Create(Owner + "nonsplit_extension_r_cycle_of_certificate"),
                H("A row-splice certificate assembles the ambient R-cycle"),
                StatementSource.FromAuthor(Disp(F.Id("assembly"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The certificate records the row successor, its complete difference map, "
                    + "and arbitrary representative transport. Conjugating the row permutation "
                    + "produces a successor on E fixing zero; its nonzero cycle and directed "
                    + "differences are carried through the same transport."))),
                DescribeRole.Theorem))));
}
