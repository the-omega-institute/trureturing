using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Zeta.NumberField;

internal sealed class ZetaProductAnalyticDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/cbirkbeck2026chebotarev");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Analytic Extension of Nontrivial Cyclotomic Artin Series.",
        H("Analytic Extension of Nontrivial Cyclotomic Artin Series"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("artin-l-series-analytic-extension"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Zeta/NumberField/ZetaProductAnalytic.artinLSeries_analytic_extension"),
                H("Analytic Extension of Nontrivial Cyclotomic Artin Series"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For a nontrivial character of a cyclotomic Galois extension L/K with m modulo four " +
                    "unequal to two, there is a function analytic on the half-plane Re(s) > 1 - 1/[K:Q]. " +
                    "On Re(s) > 1 it agrees with the Dirichlet series weighted by the character on nonzero " +
                    "ideals of K."))),
                DescribeRole.Theorem)
        )));
}
