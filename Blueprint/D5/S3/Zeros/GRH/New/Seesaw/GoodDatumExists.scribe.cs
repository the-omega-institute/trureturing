using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Seesaw;

internal sealed class GoodDatumExistsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Good Datum Exists", H("Good Datum Exists"),
        Blocks(
            Paragraph(Text("Constant terms of the chain's finite data are admissible sums with controlled denominators. An invariant admissible combination yields a good datum computing the definite chain.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Seesaw/GoodDatumExists.exists_isGoodDatum_of_invariant"),
                H("exists_isGoodDatum_of_invariant"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For a twist ϑ, q = ∏_Q Nv, let w be an admissible combination of the Data.reducedVacuum t, t in Data.admissibleTranslations q (denominator 1, size ≤ Data.cutBound^{3m} if Q = ∅), fixed by ∏ K_j with last component 1. Then for some good datum Ψ the chain of paired lifts with datum w equals ∑_t Ψ(t)·(chain with data Data.translateDatum t) on all smooth forms on X₀.")))))));
}
