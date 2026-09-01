using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeObserver;

internal sealed class FourthStageUnifiedTheoremMapDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/PrimeObserver/FourthStageUnifiedTheoremMap."
            + "fourth_stage_unified_theorem_map";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The fourth stage links observable algebras, finite quotients, coding, class "
            + "groups, and spectral limits.",
        H("The Fourth-Stage Unified Theorem Map"),
        Blocks(Describe.Lean(
            DescribeId.Create("fourth-stage-unified-theorem-map"),
            DeclarationHandle.Create(Declaration),
            H("Static, finite-quotient, coding, valuation, and spectral chains"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Observable events are the powerset of the realized image, while "
                        + "refinement is equivalent to inclusion of pullback algebras.")),
                Paragraph(Text(
                    "For finite groups, prime-power residual triviality is nilpotence; "
                        + "conjugacy-invariant separation has an exact finite success rate.")),
                Paragraph(Text(
                    "The bounded CRT code has exact distance n minus its largest blind "
                        + "coordinate count and uniquely decodes within the joint "
                        + "error-erasure budget.")),
                Paragraph(Text(
                    "Principal-trivial ideal homomorphisms descend uniquely to the class "
                        + "group under the Dedekind hypotheses.")),
                Paragraph(Text(
                    "Cayley-Hamilton controls higher traces once the characteristic "
                        + "polynomial is fixed, but a concrete Jordan witness shows that "
                        + "all power traces still do not determine similarity."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula() => Disp(Seq(
        F.Id("ObservableAlgebraRepresentation"),
        Sp, Land, Sp,
        Grp(F.Id("Refinement"), Sp, Iff, Sp, F.Id("PullbackInclusion")),
        Sp, Land, Sp,
        Grp(F.Id("PrimePowerResidualTrivial"), Sp, Iff, Sp, F.Id("Nilpotent")),
        Sp, Land, Sp,
        F.Id("ConjugacyClassSuccessRate"),
        Sp, Land, Sp,
        F.Id("ExactResidueDistance"),
        Sp, Land, Sp,
        F.Id("ErrorErasureDecoding"),
        Sp, Land, Sp,
        F.Id("ClassGroupQuotient"),
        Sp, Land, Sp,
        F.Id("TraceSaturation"),
        Sp, Land, Sp,
        F.Id("NonSimilarityWitness"), Dot));
}
