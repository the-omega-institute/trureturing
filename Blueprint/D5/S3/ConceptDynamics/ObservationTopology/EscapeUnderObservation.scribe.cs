using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ObservationTopology;

internal sealed class EscapeUnderObservationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/ObservationTopology/EscapeUnderObservation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Injective observation preserves escapes; noninjective hides one on inhabited "
            + "input.",
        H("Escape Under Observation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("injective-observations-preserve-catalog-escape"),
                DeclarationHandle.Create(Prefix + "injective_preserves_catalog_escape"),
                H("Injective observation preserves every displayed catalog escape"),
                StatementSource.FromAuthor(PreservationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Postcomposition applies the same observation to every catalog row "
                            + "and to the candidate.")),
                    Paragraph(Text(
                        "If an observed candidate agreed with an observed row, injectivity "
                            + "would recover pointwise agreement before observation.")),
                    Paragraph(Text(
                        "That recovered equality contradicts the supplied CatalogEscape. "
                            + "The conclusion therefore retains both the injectivity and "
                            + "original-escape hypotheses."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noninjective-observation-hides-an-escape"),
                DeclarationHandle.Create(Prefix + "noninjective_hides_some_catalog_escape"),
                H("Every noninjective observation hides a one-row escape"),
                StatementSource.FromAuthor(HidingFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume the input carrier is inhabited and the observation is not "
                            + "injective. Choose distinct outputs with the same observation.")),
                    Paragraph(Text(
                        "A constant one-row catalog at the first output omits the constant "
                            + "candidate at the second output; inhabitedness detects their "
                            + "difference.")),
                    Paragraph(Text(
                        "After observation the two constant functions agree, so the genuine "
                            + "escape lies in the observed catalog range. The theorem asserts "
                            + "existence of this catalog and candidate, not that every escape "
                            + "is hidden."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula PreservationFormula()
    {
        Formula index = F.Id("Index");
        Formula input = F.Id("Input");
        Formula output = F.Id("Output");
        Formula observation = F.Id("Observation");
        Formula observe = F.Id("observe");
        Formula catalog = F.Id("catalog");
        Formula candidate = F.Id("candidate");
        Formula hypotheses = Seq(
            Call("Injective", observe), Sp, Land, Sp,
            Call("CatalogEscape", catalog, candidate));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, observe, Colon, Sp, Arrow(output, observation), Comma, Sp,
            catalog, Colon, Sp, Arrow(index, Arrow(input, output)), Comma,
            RowBreak, Grp(),
            candidate, Colon, Sp, Arrow(input, output), Comma, Sp,
            Open, hypotheses, Close, Sp, Rightarrow, RowBreak, Grp(),
            Call(
                "CatalogEscape",
                Call("observedCatalog", observe, catalog),
                Call("observedCandidate", observe, candidate)),
            Dot, End, Grp(F.Id("gathered"))));
    }

    private static Formula HidingFormula()
    {
        Formula input = F.Id("Input");
        Formula output = F.Id("Output");
        Formula observation = F.Id("Observation");
        Formula observe = F.Id("observe");
        Formula catalog = F.Id("catalog");
        Formula candidate = F.Id("candidate");
        Formula catalogType = Arrow(F.Id("Unit"), Arrow(input, output));
        Formula candidateType = Arrow(input, output);
        Formula observedMembership = Call(
            "Mem",
            Call("observedCandidate", observe, candidate),
            Call("range", Call("observedCatalog", observe, catalog)));
        Formula witnessClaims = Seq(
            Call("CatalogEscape", catalog, candidate), Sp, Land, Sp,
            observedMembership);
        Formula conclusion = Seq(
            Exists, Sp, catalog, Colon, Sp, catalogType, Comma, Sp,
            Exists, Sp, candidate, Colon, Sp, candidateType, Comma, Sp,
            Open, witnessClaims, Close);
        Formula hypotheses = Seq(
            Call("Nonempty", input), Sp, Land, Sp,
            Neg, Sp, Call("Injective", observe));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, observe, Colon, Sp, Arrow(output, observation), Comma,
            RowBreak, Grp(),
            Open, hypotheses, Close, Sp, Rightarrow, RowBreak, Grp(),
            Open, conclusion, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
