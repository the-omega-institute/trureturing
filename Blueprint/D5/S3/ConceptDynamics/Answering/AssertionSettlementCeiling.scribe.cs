using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Answering;

internal sealed class AssertionSettlementCeilingDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Answering/AssertionSettlementCeiling.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "First-match settlement of an assertion record bounds its permitted public claim, and "
            + "an audited render never exceeds that ceiling while disclosing only the record.",
        H("Assertion Settlement Ceiling"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("first-match-settlement-is-exhaustive-and-single-valued"),
                DeclarationHandle.Create(DeclarationPrefix + "settle_first_match"),
                H("First-match settlement is exhaustive and single-valued"),
                StatementSource.FromAuthor(FirstMatchFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "An assertion record carries a clause-shape classification fixed at "
                            + "inventory time, whether a Lean statement exists, whether one "
                            + "current canonical build succeeded, whether the compiled statement "
                            + "is exact P or its exact negation, and how many named empirical or "
                            + "metaphysical premises remain undischarged.")),
                    Paragraph(Text(
                        "Settlement applies five ordered rules: not-formalized for a "
                            + "not-formalizable record without a Lean statement, conditional for "
                            + "compiled P with an undischarged premise, proved for compiled P "
                            + "with none, refuted for a compiled negation, and open otherwise. "
                            + "Each outcome is characterized exactly by the first rule it "
                            + "matches, so every record receives one outcome and no record "
                            + "receives two.")),
                    Paragraph(Text(
                        "This is the formal shape of Step 5 of the codex-formal-answer skill. "
                            + "It fixes how evidence maps to an outcome; it does not decide "
                            + "whether any particular Lean statement is the user's P, which "
                            + "remains the statement-echo judgment of Step 3."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("a-failed-build-settles-nothing"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "failed_build_settles_open_or_not_formalized"),
                H("A failed build settles nothing"),
                StatementSource.FromAuthor(FailedBuildFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Both compiled-P and compiled-negation conditions require a successful "
                        + "build, so a failed or unavailable build can only reach the open "
                        + "rule or the earlier not-formalized rule. A proof text that did not "
                        + "compile therefore neither proves nor refutes anything."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("formalizability-is-independent-of-the-build"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "not_formalized_independent_of_build"),
                H("Formalizability is independent of the build"),
                StatementSource.FromAuthor(IndependenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Two records with the same classification and the same statement "
                        + "presence settle not-formalized together, whatever their build and "
                        + "proof fields. Capability failure, proof difficulty, and elapsed "
                        + "effort cannot reclassify a clause."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("an-open-record-permits-only-the-unsettled-claim"),
                DeclarationHandle.Create(DeclarationPrefix + "open_permits_only_unsettled"),
                H("An open record permits only the unsettled claim"),
                StatementSource.FromAuthor(OpenCeilingFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Claims are ordered by commitment: the unsettled claim conveys nothing "
                        + "about P, the conditional consequent lies below exact P, and other "
                        + "claims compare only with themselves. The open outcome has the "
                        + "unsettled claim as its ceiling, so it permits neither P, nor its "
                        + "negation, nor a conditional consequent."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("a-permitted-formal-claim-is-backed-by-a-successful-build"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "formal_claim_requires_successful_build"),
                H("A permitted formal claim is backed by a successful build"),
                StatementSource.FromAuthor(CeilingSoundnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Only the proved, refuted, and conditional outcomes permit a "
                            + "formal-grade claim, and each of those outcomes is characterized "
                            + "by a compiled statement, which requires a successful build.")),
                    Paragraph(Text(
                        "This is ceiling soundness for the answer register: whatever formal "
                            + "claim the maximum permitted claim licenses, one successful "
                            + "current build of the exact statement stands behind it. It says "
                            + "nothing about claims a renderer might convey outside the "
                            + "register; that gap is closed by the audited renderer below."))),
                DescribeRole.Theorem),
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

    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Or, right);

    private static Formula ImpliesFormula(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula IffFormula(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Settle(Formula evidence) => Call("settle", evidence);

    private static Formula IsTrue(Formula value) => Equal(value, F.Id("true"));

    private static Formula IsFalse(Formula value) => Equal(value, F.Id("false"));

    private static Formula MemberOf(Formula element, Formula list) =>
        new Formula.Relation(element, FormulaRelationOperator.MemberOf, list);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

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

    private static Formula FirstMatchFormula()
    {
        Formula e = F.Id("e");
        Formula rule = Call("notFormalizedRule", e);
        Formula compiledP = Call("compiledP", e);
        Formula compiledNegP = Call("compiledNegP", e);
        Formula undischarged = Call("undischarged", e);
        Formula notFormalized = IffFormula(
            Equal(Settle(e), F.Id("notFormalized")),
            IsTrue(rule));
        Formula conditional = IffFormula(
            Equal(Settle(e), F.Id("conditional")),
            And(IsFalse(rule), And(
                IsTrue(compiledP),
                new Formula.Relation(Num(0), FormulaRelationOperator.LessThan, undischarged))));
        Formula proved = IffFormula(
            Equal(Settle(e), F.Id("proved")),
            And(IsFalse(rule), And(IsTrue(compiledP), Equal(undischarged, Num(0)))));
        Formula refuted = IffFormula(
            Equal(Settle(e), F.Id("refuted")),
            And(IsFalse(rule), And(IsFalse(compiledP), IsTrue(compiledNegP))));
        Formula open = IffFormula(
            Equal(Settle(e), F.Id("open")),
            And(IsFalse(rule), And(IsFalse(compiledP), IsFalse(compiledNegP))));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("e", F.Id("Evidence"))],
            And(notFormalized, And(conditional, And(proved, And(refuted, open))))));
    }

    private static Formula FailedBuildFormula()
    {
        Formula e = F.Id("e");

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("e", F.Id("Evidence"))],
            ImpliesFormula(
                IsFalse(Call("buildSucceeded", e)),
                Or(
                    Equal(Settle(e), F.Id("open")),
                    Equal(Settle(e), F.Id("notFormalized"))))));
    }

    private static Formula IndependenceFormula()
    {
        Formula e = F.Id("e");
        Formula f = F.Id("f");

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("e", F.Id("Evidence")), Bound("f", F.Id("Evidence"))],
            ImpliesFormula(
                And(
                    Equal(Call("classification", e), Call("classification", f)),
                    Equal(Call("hasLeanStatement", e), Call("hasLeanStatement", f))),
                IffFormula(
                    Equal(Settle(e), F.Id("notFormalized")),
                    Equal(Settle(f), F.Id("notFormalized"))))));
    }

    private static Formula OpenCeilingFormula()
    {
        Formula c = F.Id("c");

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("c", F.Id("Claim"))],
            IffFormula(
                IsTrue(Call("permits", F.Id("open"), c)),
                Equal(c, F.Id("unsettled")))));
    }

    private static Formula CeilingSoundnessFormula()
    {
        Formula e = F.Id("e");
        Formula c = F.Id("c");

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("e", F.Id("Evidence")), Bound("c", F.Id("Claim"))],
            ImpliesFormula(
                And(
                    IsTrue(Call("isFormal", c)),
                    IsTrue(Call("permits", Settle(e), c))),
                IsTrue(Call("buildSucceeded", e)))));
    }

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
                            Settle(EvidenceOf(takeaway)),
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
                        Equal(Settle(EvidenceOf(takeaway)), F.Id("open")),
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
