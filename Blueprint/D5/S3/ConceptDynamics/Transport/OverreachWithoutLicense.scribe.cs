using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Transport;

internal sealed class OverreachWithoutLicenseDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Transport/OverreachWithoutLicense.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Licensed reports retain transport conditions and expansion reopens completion.",
        H("Transport Licensing and Scope Overreach"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("overreach-without-license"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "overreach_without_license"),
                H("Unlicensed scope expansion is overreach"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A transport report q stores concept(q), its claimed operation scope J', "
                            + "and its retained proposition condition(q). LicensedReport also checks "
                            + "that the stored scope equals the explicit J', so the target domain "
                            + "cannot drift through a free argument.")),
                    Paragraph(Text(
                        "ValidTransportCert is the concrete predicate imported from the transport-"
                            + "certificate validity module. Its arguments bind the certificate to "
                            + "the source record r, concept(q), old and claimed scopes, and "
                            + "Version(concept(q)); this module introduces no second validity "
                            + "definition.")),
                    Paragraph(Text(
                        "A license retains condition(q) exactly as GivenPremises(kappa) conjoined "
                            + "with the certificate's explicit transport-assumption obligations. "
                            + "Therefore an unconditional "
                            + "licensed report exposes proofs of both conjuncts, while a missing "
                            + "conjunct prevents the condition from being discharged.")),
                    Paragraph(Text(
                        "Overreach is the conjunction of strict scope expansion, "
                            + "Scope(concept(q))=J, the report's claim of J', and absence of a "
                            + "license. No certificate validity or premise is inferred from the "
                            + "scope equations.")),
                    Paragraph(Text(
                        "Section 35 informally assumes that the record space carries a distance, "
                            + "but it does not declare the comparison and supremum operations on "
                            + "abstract Delta, or the laws for those operations, that Lean needs "
                            + "for the later <= epsilon and above-epsilon notation. The tolerance "
                            + "clause is therefore not a conjunct of this theorem. A checked Boolean "
                            + "false neighbor records only that old-scope tolerance can fail after "
                            + "strict expansion. This paragraph and the matching module comment are "
                            + "human-readable only: they register neither digestion coverage nor an "
                            + "unresolved subitem. Ingest currently has no path for a newly discovered "
                            + "unresolved subitem; issue #3066 tracks that machine-registration gap.")),
                    Paragraph(Text(
                        "CAS defines Closed_J(S,T) exactly by emptiness of defectRelation after "
                            + "restricting S and T to J. A concrete two-operation witness has an "
                            + "empty residual on its old singleton scope and a nonempty residual "
                            + "on the expanded scope, so expansion reopens local completion.")),
                    Paragraph(Text(
                        "Conversely, when the report's stored scope equals the claimed scope, a "
                            + "valid certificate together "
                            + "with every given premise and its transport assumption licenses the "
                            + "condition-update q[condition := True]. Without the premise and "
                            + "assumption proofs, the exact conditional statement remains the only "
                            + "licensed form.")),
                    Paragraph(Text(
                        "Repository type-shape, English and Chinese synonym, and neighboring-module "
                            + "searches found no transport-license or overreach definition. "
                            + "Concept and the canonical defectRelation are reused; no "
                            + "second residual or closure predicate is introduced."))),
                DescribeRole.Theorem))));

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula StrictSubset(Formula subset, Formula superset) =>
        Grp(
            subset, Sp, Subset, Sp, superset, Sp, Land, Sp,
            subset, Sp, Neq, Sp, superset);

    private static Formula UpdateCondition(Formula report, Formula condition) =>
        Seq(
            report, OpenBracket,
            Operatorname, Grp(F.Id("condition")), Sp, Colon, Eq, Sp, condition,
            CloseBracket);

    private static Formula TheoremFormula()
    {
        Formula q = F.Id("q");
        Formula record = F.Id("r");
        Formula oldScope = F.Id("J");
        Formula claimedScope = Seq(F.Id("J"), Apos);
        Formula certificate = Kappa;
        Formula reportConcept = Call("concept", q);
        Formula reportCondition = Call("condition", q);
        Formula trueCondition = Seq(Mathrm, Grp(F.Id("True")));
        Formula deconditionedReport = UpdateCondition(q, trueCondition);
        Formula licensed = Call("LicensedReport", q, oldScope, claimedScope);
        Formula validCertificate = Call(
            "ValidTransportCert",
            certificate,
            record,
            reportConcept,
            oldScope,
            claimedScope,
            Call("Version", reportConcept));
        Formula premises = Call("GivenPremises", certificate);
        Formula assumption = Call(
            "Holds",
            Call("TransportAssumption", certificate));
        Formula completeCondition = Grp(
            reportCondition, Sp, Iff, Sp, premises, Sp, Land, Sp, assumption);
        Formula reportScope = Call("reportedScope", q);
        Formula licenseDefinition = Grp(
            licensed, Sp, Iff, Sp,
            reportScope, Sp, Eq, Sp, claimedScope, Sp, Land, Sp,
            Exists, Sp, certificate, Comma, Sp,
            validCertificate, Sp, Land, Sp, completeCondition);
        Formula unconditionalDuty = Grp(
            licensed, Sp, Rightarrow, Sp, reportCondition, Sp, Rightarrow, Sp,
            Exists, Sp, certificate, Comma, Sp,
            validCertificate, Sp, Land, Sp, premises, Sp, Land, Sp, assumption);
        Formula retainedCondition = Grp(
            licensed, Sp, Rightarrow, Sp,
            Exists, Sp, certificate, Comma, Sp,
            validCertificate, Sp, Land, Sp, completeCondition, Sp, Land, Sp,
            Open, Open, Neg, premises, Sp, Lor, Sp, Neg, assumption, Close,
            Sp, Rightarrow, Sp, Neg, reportCondition, Close);
        Formula overreachDefinition = Grp(
            Call("Overreach", q, oldScope, claimedScope), Sp, Iff, Sp,
            StrictSubset(oldScope, claimedScope), Sp, Land, Sp,
            Call("Scope", reportConcept), Sp, Eq, Sp, oldScope, Sp, Land, Sp,
            reportScope, Sp, Eq, Sp, claimedScope, Sp, Land, Sp,
            Neg, licensed);
        Formula closureCounterexample = ClosureCounterexample();
        Formula deconditioning = Grp(
            Forall, Sp, certificate, Comma, Sp,
            reportScope, Sp, Eq, Sp, claimedScope, Sp, Rightarrow, Sp,
            validCertificate, Sp, Rightarrow, Sp,
            premises, Sp, Rightarrow, Sp,
            assumption, Sp, Rightarrow, Sp,
            Call("LicensedReport", deconditionedReport, oldScope, claimedScope));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            licenseDefinition, Sp, Land, RowBreak, Grp(),
            unconditionalDuty, Sp, Land, RowBreak, Grp(),
            retainedCondition, Sp, Land, RowBreak, Grp(),
            overreachDefinition, Sp, Land, RowBreak, Grp(),
            closureCounterexample, Sp, Land, RowBreak, Grp(),
            deconditioning, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula ClosureCounterexample()
    {
        Formula oldScope = Subscript(F.Id("J"), D(0));
        Formula claimedScope = Subscript(F.Id("J"), D(1));
        Formula system = F.Id("S");
        Formula target = F.Id("T");
        Formula oldResidual = Call(
            "defectRelation",
            Call("restrict", system, oldScope),
            Call("restrict", target, oldScope));
        Formula claimedResidual = Call(
            "defectRelation",
            Call("restrict", system, claimedScope),
            Call("restrict", target, claimedScope));

        return Grp(
            Exists, Sp, oldScope, Comma, Sp, claimedScope, Comma, Sp,
            system, Comma, Sp, target, Comma, Sp,
            StrictSubset(oldScope, claimedScope), Sp, Land, Sp,
            oldResidual, Sp, Eq, Sp, Emptyset, Sp, Land, Sp,
            claimedResidual, Sp, Neq, Sp, Emptyset);
    }
}
