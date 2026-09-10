using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DependencyTopology;

internal sealed class LegalLedgerFixedSetDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/DependencyTopology/LegalLedgerFixedSet.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed membership of legal proof ledgers under witness-preserving extensions.",
        H("Legal Ledger Fixed Set"),
        Blocks(
            Paragraph(Text(
                "Let P, Proof, Ax and Model be arbitrary types, and let k be kernel data. "
                + "The kernel accepts or rejects each proof of a proposition and reads its "
                + "finite sets of axioms and direct references. Proved means that an accepted "
                + "proof uses only permitted axioms.")),
            Paragraph(Text(
                "A certified core has finitely many nodes, an exact witness for each node, "
                + "accepted witnesses using permitted axioms, closure under their actual "
                + "references, and an acyclic reference relation. A certificate for a "
                + "proposition is such a core containing it. A legal ledger adds an arbitrary "
                + "registered frontier disjoint from its core; the frontier need not be finite.")),
            Paragraph(Text(
                "An extension retains every old node, every derived edge, and the exact old "
                + "witness. A transformation is a total map on all legal ledgers, and it is "
                + "admissible when it is an extension on every input. Fix consists of propositions "
                + "whose frozen membership is invariant under every such admissible map.")),
            Describe.Lean(
                DescribeId.Create("certificate-append-is-admissible"),
                DeclarationHandle.Create(Prefix + "addWithCertificate_admissible"),
                H("A certificate gives an admissible total transformation"),
                StatementSource.FromAuthor(AdmissibleFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The transformation is the identity when the proposition is already "
                        + "frozen. Otherwise it takes the finite union of the old core and the "
                        + "certificate, keeps old witnesses on every overlap, and uses certificate "
                        + "witnesses only for new nodes. It removes certificate nodes from the frontier.")),
                    Paragraph(Text(
                        "Old nodes reference only old nodes. Edges between new nodes are "
                        + "certificate edges. Tagging old and new nodes by the two sides of a "
                        + "lexicographic sum maps each selected-witness edge into an irreflexive "
                        + "transitive relation. The transitive-closure lifting theorem rules out "
                        + "cycles. Acceptance, axiom permission and reference closure follow "
                        + "from whichever witness was selected, without an overlap compatibility premise.")),
                    Paragraph(Text(
                        "The resulting ledger is legal for every legal input and retains "
                        + "all old nodes, edges and witnesses."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fixed-is-frozen-or-unprovable"),
                DeclarationHandle.Create(Prefix + "fixed_eq_frozen_union_unprovable"),
                H("Fixed membership is frozen or unprovable membership"),
                StatementSource.FromAuthor(FixedSetFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "SourceLaws includes kernel soundness in every permitted-axiom model, "
                        + "certificate existence for every proved proposition, and consistency: "
                        + "a proposition and its negation cannot both be proved. All three remain "
                        + "explicit in the theorem contract. The structural argument uses the "
                        + "certificate-existence conjunct.")),
                    Paragraph(Text(
                        "Frozen propositions stay frozen by admissibility. An unprovable "
                        + "proposition cannot appear in any legal core, since its selected "
                        + "witness would prove it. Hence both kinds have invariant membership.")),
                    Paragraph(Text(
                        "Conversely, an unfrozen proved proposition has a certificate. The "
                        + "admissible certificate transformation makes it frozen, contradicting "
                        + "invariance. This argument quantifies over all legal ledgers and all "
                        + "total admissible transformations; it makes no claim about record "
                        + "ledgers or transformations that permit invalid witnesses."))),
                DescribeRole.Theorem))));

    private static Formula AdmissibleFormula()
    {
        Formula k = F.Id("k");
        Formula p = F.Id("p");
        Formula certificate = F.Id("C");
        return Disp(Seq(
            Forall, Sp, p, Colon, Sp, F.Id("P"), Comma, Sp,
            Forall, Sp, certificate, Colon, Sp, Call("Certificate", k, p), Comma, Sp,
            Call("Admissible", Call("addWithCertificate", p, certificate)), Dot));
    }

    private static Formula FixedSetFormula()
    {
        Formula k = F.Id("k");
        Formula ledger = F.Id("L");
        Formula p = F.Id("p");
        Formula unprovable = Seq(
            OpenBrace, p, Colon, Sp, F.Id("P"), Sp, Mid, Sp,
            Neg, Sp, Call("Proved", k, p), CloseBrace);
        return Disp(Seq(
            Forall, Sp, F.Id("laws"), Colon, Sp, Call("SourceLaws", k), Comma, Sp,
            Forall, Sp, ledger, Colon, Sp, Call("LegalLedger", k), Comma, Sp,
            Call("Fix", ledger), Sp, Eq, Sp,
            Call("Frozen", ledger), Sp, Cup, Sp, unprovable, Dot));
    }
}
