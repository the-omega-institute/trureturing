using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Shimura.IntegralModel;

internal sealed class UniversalPointsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Universal Points", H("Universal Points"),
        Blocks(
            Paragraph(Text("Deep principal levels for finitely many isogenies; finite torsion index sets. Hecke isogenies at a split place: multiplier, action on level points, kernel in w-torsion. Kuga–Sato fibre powers, their complex points up to isomorphism, and level covers as closures.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Shimura/IntegralModel/UniversalPoints.fibrePower_spec"),
                H("fibrePower_spec"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The ν-fold fibre power Z of the universal family is smooth over R of relative dimension |n| − 1 + ν|n|[E⁺:ℚ]; its complex points [a] (UniversalFamily.datumPoint, 𝔪 = 1) are dense, and R-endomorphisms m_α of Z send [a·(g,1)] to [a·(g,α)].")))))));
}
