using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Provenance;

internal sealed class SourceCutsetHittingDualityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Source cuts are exactly hitting sets of all minimal proof supports.",
        H("Source-Cutset Hitting Duality"),
        Blocks(Describe.Lean(
            DescribeId.Create("source-cutset-hitting-duality"),
            DeclarationHandle.Create(
                "D5/S3/ConceptDynamics/Provenance/SourceCutsetHittingDuality."
                    + "source_cutset_hitting_duality"),
            H("Source cuts and minimal-support hitting sets have the same minimum size"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The finite source carrier and monotone provability predicate are the source "
                        + "primitives. A minimal proof support is a proving finite set with no "
                        + "proper proving subset. A source cut is a removal whose finite complement "
                        + "does not prove the conclusion.")),
                Paragraph(Text(
                    "If a cut missed a minimal support, monotonicity would make the remaining "
                        + "sources prove the conclusion. Conversely, any proving remainder has a "
                        + "least-cardinality proving subset, and that minimal support contradicts "
                        + "the claim that every minimal support was hit.")),
                Paragraph(Text(
                    "Proof resilience and minimum hitting cardinality are defined separately as "
                        + "natural infima. The cut-hitting equivalence identifies their candidate "
                        + "cardinality sets and therefore their minima."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula TheoremFormula()
    {
        Formula source = F.Id("Source");
        Formula provable = F.Id("P");
        Formula removed = F.Id("H");
        Formula finsetSource = Apply(F.Id("Finset"), source);
        Formula sourceCut = Apply(F.Id("IsSourceCut"), provable, removed);
        Formula hits = Apply(F.Id("HitsEveryMinimalProofSupport"), provable, removed);
        Formula duality = Seq(
            Forall, Sp, Typed(removed, finsetSource), Comma, Sp,
            sourceCut, Sp, Iff, Sp, hits);
        Formula minima = Seq(
            Apply(F.Id("proofResilience"), provable), Sp, Eq, Sp,
            Apply(F.Id("minimumHittingCardinality"), provable));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Typed(source, Seq(Operatorname, Grp(F.Id("Type")))), Comma, Sp,
            Typed(provable, Arrow(finsetSource, F.Id("Prop"))), Comma, RowBreak, Grp(),
            Apply(F.Id("Fintype"), source), Sp, Land, Sp,
            Apply(F.Id("DecidableEq"), source), Sp, Land, Sp,
            Apply(F.Id("Monotone"), provable), Sp, Rightarrow, RowBreak, Grp(),
            Open, duality, Close, Sp, Land, RowBreak, Grp(),
            minima, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
