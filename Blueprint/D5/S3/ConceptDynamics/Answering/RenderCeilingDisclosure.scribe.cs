using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Answering;

internal sealed class RenderCeilingDisclosureDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Answering/RenderCeilingDisclosure.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An audited render never exceeds the register ceiling and discloses only the record.",
        H("Render Ceiling Disclosure"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("every-emitted-takeaway-is-within-the-register-ceiling"),
                DeclarationHandle.Create(DeclarationPrefix + "rendered_takeaway_within_ceiling"),
                H("Every emitted takeaway is within the register ceiling"),
                StatementSource.FromAuthor(WithinCeilingFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A draft is a list of competent-reader takeaways, each naming the "
                            + "assertion key it is about and the claim a reader would take "
                            + "away. The register maps each key to the evidence of its unique "
                            + "active record, and the renderer emits the draft only when every "
                            + "takeaway is permitted by the settled outcome of its key.")),
                    Paragraph(Text(
                        "The theorem fixes the shape of Step 7 of the codex-formal-answer "
                            + "skill. The mapping from prose to takeaways is a worker judgment "
                            + "outside this model; the model guarantees only that whatever the "
                            + "worker maps is bounded by the register."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("every-emitted-formal-claim-is-compiled"),
                DeclarationHandle.Create(DeclarationPrefix + "rendered_formal_claim_is_compiled"),
                H("Every emitted formal claim is compiled"),
                StatementSource.FromAuthor(CompiledFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Composing the audit with ceiling soundness: any formal-grade claim that "
                        + "an emitted answer conveys about an assertion is backed by one "
                        + "successful current build of the exact statement it is about. "
                        + "Search hits, prose synthesis, and unbuilt proof texts cannot reach "
                        + "the reader as formal claims."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("an-open-assertion-blocks-emission"),
                DeclarationHandle.Create(DeclarationPrefix + "open_key_blocks_emission"),
                H("An open assertion blocks emission"),
                StatementSource.FromAuthor(OpenBlocksFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If any takeaway conveys more than the unsettled claim about an open "
                        + "assertion, the audit fails and nothing is emitted in either "
                        + "disclosure mode. An open assertion may be reported only as "
                        + "unsettled, never as P, its negation, or a conditional consequent."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("disclosure-changes-the-attachment-not-the-claims"),
                DeclarationHandle.Create(DeclarationPrefix + "disclosure_preserves_claims"),
                H("Disclosure changes the attachment, not the claims"),
                StatementSource.FromAuthor(DisclosureFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The plain answer and the show-work answer pass the same audit and carry "
                        + "the same prose; the disclosure switch decides only whether the "
                        + "internal run record is attached. Asking to see the reasoning "
                        + "therefore never strengthens or weakens what the answer claims."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("show-work-attaches-the-record"),
                DeclarationHandle.Create(DeclarationPrefix + "show_work_exposes_record"),
                H("Show-work attaches the record"),
                StatementSource.FromAuthor(ShowWorkFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "In show-work mode an emitted answer carries the internal record, and "
                        + "the companion lemma for plain mode shows it carries none. What is "
                        + "disclosed is the record itself, not a fresh narrative about it."))),
                DescribeRole.Lemma))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula ImpliesFormula(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula MemberOf(Formula element, Formula list) =>
        new Formula.Relation(element, FormulaRelationOperator.MemberOf, list);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula IsTrue(Formula value) => Equal(value, F.Id("true"));

    private static Formula Some(Formula value) => Call("some", value);

    private static Formula Render(Formula mode) =>
        Call("render", F.Id("R"), F.Id("w"), mode, F.Id("d"));

    private static Formula EvidenceOf(Formula takeaway) =>
        Apply(F.Id("R"), Call("key", takeaway));

    private static Formula.BoundVariable[] Context() =>
        [
            Bound("K", F.Id("Type")),
            Bound("W", F.Id("Type")),
            Bound("R", Arrow(F.Id("K"), F.Id("Evidence"))),
            Bound("w", F.Id("W")),
            Bound("d", Call("List", Call("Takeaway", F.Id("K")))),
        ];

    private static Formula WithinCeilingFormula()
    {
        Formula takeaway = F.Id("t");
        Formula output = F.Id("o");

        return Disp(ForAll(
            [
                .. Context(),
                Bound("m", F.Id("Disclosure")),
                Bound("o", Call("Output", F.Id("K"), F.Id("W"))),
            ],
            ImpliesFormula(
                Equal(Render(F.Id("m")), Some(output)),
                ForAll(
                    [Bound("t", Call("Takeaway", F.Id("K")))],
                    ImpliesFormula(
                        MemberOf(takeaway, Call("prose", output)),
                        IsTrue(Call(
                            "permits",
                            Call("settle", EvidenceOf(takeaway)),
                            Call("claim", takeaway))))))));
    }

    private static Formula CompiledFormula()
    {
        Formula takeaway = F.Id("t");
        Formula output = F.Id("o");

        return Disp(ForAll(
            [
                .. Context(),
                Bound("m", F.Id("Disclosure")),
                Bound("o", Call("Output", F.Id("K"), F.Id("W"))),
            ],
            ImpliesFormula(
                Equal(Render(F.Id("m")), Some(output)),
                ForAll(
                    [Bound("t", Call("Takeaway", F.Id("K")))],
                    ImpliesFormula(
                        And(
                            MemberOf(takeaway, Call("prose", output)),
                            IsTrue(Call("isFormal", Call("claim", takeaway)))),
                        IsTrue(Call("buildSucceeded", EvidenceOf(takeaway))))))));
    }

    private static Formula OpenBlocksFormula()
    {
        Formula takeaway = F.Id("t");

        return Disp(ForAll(
            [.. Context(), Bound("m", F.Id("Disclosure")), Bound("t", Call("Takeaway", F.Id("K")))],
            ImpliesFormula(
                And(
                    MemberOf(takeaway, F.Id("d")),
                    And(
                        Equal(Call("settle", EvidenceOf(takeaway)), F.Id("open")),
                        NotEqual(Call("claim", takeaway), F.Id("unsettled")))),
                Equal(Render(F.Id("m")), F.Id("none")))));
    }

    private static Formula DisclosureFormula() =>
        Disp(ForAll(
            Context(),
            Equal(
                Call("map", F.Id("prose"), Render(F.Id("plain"))),
                Call("map", F.Id("prose"), Render(F.Id("showWork"))))));

    private static Formula ShowWorkFormula()
    {
        Formula output = F.Id("o");

        return Disp(ForAll(
            [.. Context(), Bound("o", Call("Output", F.Id("K"), F.Id("W")))],
            ImpliesFormula(
                Equal(Render(F.Id("showWork")), Some(output)),
                Equal(Call("record", output), Some(F.Id("w"))))));
    }
}
