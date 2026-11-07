using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.Cryptids;

internal sealed class VonMangoldtCountDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "VonMangoldtCount analytic source: VonMangoldtCount", H("VonMangoldtCount analytic source: VonMangoldtCount"),
        Blocks(Paragraph(Text("Faithful source transplant from google-deepmind/cryptids at immutable revision e5f59ed70d1549a61ef8873a6fbae9268fdbd557, Cryptids/Semantics/Riemann/VonMangoldtCount.lean. Copyright 2026 Google LLC, Apache-2.0; the full license is docs/reports/licenses/cryptids-LICENSE.txt. Only routing and current-pin API adaptations are local. The original declaration namespace and proof ownership are preserved. This is reuse of the upstream proof, not a claim of new mathematical content. Retire this transplant when an equivalent RH-only real-variable psi estimate above 5000 is present at this repository own Mathlib revision in lake-manifest.json; directly reference that supplier and remove its unused transplanted closure.")),
            Describe.Lean(DescribeId.Create("source-conclusion"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/Cryptids/VonMangoldtCount.weightedZeroCountingFunction_eq_zero_of_le_six"),
                H("weightedZeroCountingFunction eq zero of le six"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Weil/cryptids2026rhpsi")),
                Blocks(Paragraph(Text("The exact statement and hypotheses are those of the original declaration, checked on the current project pins."))),
                DescribeRole.Theorem))));
}
