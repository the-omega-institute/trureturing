using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.CM.Genus;

internal sealed class QuadraticZetaDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Quadratic Zeta", H("Quadratic Zeta"),
        Blocks(
            Paragraph(Text("A complex number bounded under all 2-adic identifications is algebraic. Odd class number for prime discriminant; ramified prime; zeta factorisation of the quadratic field.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/CM/Genus/QuadraticZeta.classGroup_sq_bijective"),
                H("classGroup_sq_bijective"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For d a prime ≡ 7 mod 8, squaring is a bijection of the class group of ℚ(√−d); that is, the class number is odd (genus theory).")))))));
}
