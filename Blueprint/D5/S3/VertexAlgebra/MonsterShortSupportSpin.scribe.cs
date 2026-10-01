using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class MonsterShortSupportSpinDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/MonsterShortSupportSpin.";
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/basak2017monstercharactercarry");
    private static readonly LibraryNoteRef ShortSupportBackground =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/macwilliams1977binaryrepetition");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Monster labels carry a quadratic ground-section parity.",
        H("Monster Short-Support Spin Data"),
        Blocks(
            Paragraph(Text("The label quadratic is defined independently of the seven-section map. "
                + "Right-additivity identifies its value on a ground section with the diagonal sign, "
                + "and the opposite law identifies the polar pairing of distinct nonzero sections.")),
            Describe.Lean(
                DescribeId.Create("monster-ground-section-quadratic"),
                DeclarationHandle.Create(Prefix + "labelQuadratic_groundSection"),
                H("Ground-section quadratic value"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("This is a finite label theorem. It does not construct a VOA "
                    + "module, an intertwiner, an OPE coefficient, or a Monster action."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("monster-ground-section-polar"),
                DeclarationHandle.Create(Prefix + "labelQuadratic_groundSection_polar"),
                H("Distinct-section polar pairing"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(ShortSupportBackground),
                Blocks(Paragraph(Text("The proof consumes the IsSignTable opposite law, so the "
                    + "quadratic datum is not a renamed support predicate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("monster-short-support-weight"),
                DeclarationHandle.Create(Prefix + "shortWeight"),
                H("Public short-support weight"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(ShortSupportBackground),
                Blocks(Paragraph(Text("The existing unique representative theorem remains in "
                    + "MonsterShortSupport; this declaration supplies its public weight expression."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("monster-six-map-explicit"),
                DeclarationHandle.Create(Prefix + "sixMap_explicit"),
                H("Explicit six-section expansion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("This coordinate expansion is the public interface used by "
                    + "the finite full-map quadratic proof."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("monster-six-map-all-ones"),
                DeclarationHandle.Create(Prefix + "sixMap_allOnes_explicit"),
                H("All-ones six-section relation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The seven-section relation identifies the all-ones six-section "
                    + "sum with the seventh nonzero ground section."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("monster-full-map-quadratic"),
                DeclarationHandle.Create(Prefix + "labelQuadratic_fullMap"),
                H("Quadratic parity of the full seven-section map"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The proof sums over the selected support, inducts on its "
                    + "cardinality, and uses the ground-section value and distinct-section "
                    + "polar pairing. It proves the binomial parity formula in F_2. This is "
                    + "still a finite label theorem and does not construct VOA modules, fusion "
                    + "intertwiners, OPE coefficients, or conformal weights."))),
                DescribeRole.Theorem))));
}
