using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Provenance;

internal sealed class SourceCutsetInclusionMinimalHittingDualityDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Provenance/SourceCutsetInclusionMinimalHittingDuality.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Source cuts are exactly the hitting sets of the canonical family of inclusion-minimal "
            + "proof supports, with equal minimum cardinalities.",
        H("Source-Cutset Inclusion-Minimal Hitting Duality"),
        Blocks(Describe.Lean(
            DescribeId.Create("source-cutset-inclusion-minimal-hitting-duality"),
            DeclarationHandle.Create(
                DeclarationPrefix + "source_cutset_inclusion_minimal_hitting_duality"),
            H("Source cuts and canonical minimal-support hitting sets coincide"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The finite source carrier, decidable equality, and monotone provability "
                        + "predicate are explicit premises. InclusionMinimalSupport is imported "
                        + "from the canonical dependency-support family.")),
                Paragraph(Text(
                    "The displayed local predicate expands hitting every canonical minimal "
                        + "support. It is not identified with the cut predicate: the equivalence "
                        + "is inherited from the frozen source-cutset theorem through the exact "
                        + "alpha-equivalence of the old and canonical support predicates.")),
                Paragraph(Text(
                    "Proof resilience retains its independent frozen definition as the least "
                        + "source-cut cardinality. The second conjunct identifies it with the "
                        + "natural infimum of cardinalities satisfying the displayed hitting "
                        + "predicate."))),
            DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Define(Formula name, Formula value) =>
        Seq(name, Sp, Colon, Eq, Sp, value);

    private static Formula TheoremFormula()
    {
        Formula source = F.Id("Source");
        Formula provable = F.Id("P");
        Formula removed = F.Id("H");
        Formula support = F.Id("S");
        Formula size = F.Id("n");
        Formula hitsEvery = F.Id("hitsEveryInclusionMinimalSupport");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula finsetSource = Call("Finset", source);
        Formula hitIntersection = Call("Nonempty", Call("inter", removed, support));
        Formula hitsBody = Seq(
            Forall, Sp, Typed(support, finsetSource), Comma, Sp,
            Call("InclusionMinimalSupport", provable, support), Sp,
            Rightarrow, Sp, hitIntersection);
        Formula hitsDefinition = Seq(
            LambdaLower, Sp, Typed(removed, finsetSource), Comma, Sp, hitsBody);
        Formula duality = Seq(
            Forall, Sp, Typed(removed, finsetSource), Comma, Sp,
            Call("IsSourceCut", provable, removed), Sp, Iff, Sp,
            Call("hitsEveryInclusionMinimalSupport", removed));
        Formula hittingSizes = Seq(
            OpenBrace, Typed(size, naturals), Sp, Mid, Sp,
            Exists, Sp, Typed(removed, finsetSource), Comma, Sp,
            Call("hitsEveryInclusionMinimalSupport", removed), Sp, Land, Sp,
            Call("card", removed), Sp, Eq, Sp, size, CloseBrace);
        Formula minima = Seq(
            Call("proofResilience", provable), Sp, Eq, Sp,
            Call("sInf", hittingSizes));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Typed(source, type), Comma, Sp,
            Typed(provable, Arrow(finsetSource, F.Id("Prop"))), Comma, RowBreak, Grp(),
            Call("Fintype", source), Sp, Land, Sp,
            Call("DecidableEq", source), Sp, Land, Sp,
            Call("Monotone", provable), Sp, Rightarrow, RowBreak, Grp(),
            Operatorname, Grp(F.Id("let")), Sp,
            Define(hitsEvery, hitsDefinition), RowBreak, Grp(),
            Operatorname, Grp(F.Id("in")), Sp,
            Open, duality, Close, Sp, Land, RowBreak, Grp(),
            minima, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
