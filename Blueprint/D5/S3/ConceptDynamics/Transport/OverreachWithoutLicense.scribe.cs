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
                        "For a strict expansion and any preorder-valued comparison codomain Delta, "
                            + "a new operation is selected with Mathlib's ssubset witness. If "
                            + "unchanged readings remain within epsilon and the reading space admits "
                            + "an above-epsilon deviation, two records agree and fit on the local "
                            + "scope but fail on the expanded scope. No additive, metric-completeness, "
                            + "or natural-number structure is assumed.")),
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
                            + "Concept, Set.EqOn, and the canonical defectRelation are reused; no "
                            + "second residual or closure predicate is introduced."))),
                DescribeRole.Theorem))));

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var separated = new List<Formula>();
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                separated.Add(Comma);
                separated.Add(Sp);
            }

            separated.Add(arguments[index]);
        }

        return Seq(function, Open, Seq([.. separated]), Close);
    }

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
        Formula toleranceCounterexample = ToleranceCounterexample();
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
            toleranceCounterexample, Sp, Land, RowBreak, Grp(),
            closureCounterexample, Sp, Land, RowBreak, Grp(),
            deconditioning, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula ToleranceCounterexample()
    {
        Formula deviation = DeltaLower;
        Formula codomain = F.Id("Delta");
        Formula epsilon = Varepsilon;
        Formula operation = F.Id("I");
        Formula readingType = F.Id("R");
        Formula reading = F.Id("x");
        Formula ordinary = F.Id("a");
        Formula exceptional = F.Id("b");
        Formula oldScope = Subscript(F.Id("J"), D(0));
        Formula claimedScope = Subscript(F.Id("J"), D(1));
        Formula system = F.Id("S");
        Formula word = F.Id("w");
        Formula comparisonType = Seq(
            readingType, Sp, Times, Sp, readingType, Sp, To, Sp, codomain);
        Formula recordType = Seq(operation, Sp, To, Sp, readingType);

        return Grp(
            Forall, Sp, codomain, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Sp,
            OpenBracket, Operatorname, Grp(F.Id("Preorder")),
            Open, codomain, Close, CloseBracket, Comma, Esc,
            deviation, Colon, Sp, comparisonType, Comma, Sp,
            epsilon, Colon, Sp, codomain, Comma, Esc,
            oldScope, Comma, Sp, claimedScope, Colon, Sp,
            Call("Set", operation), Comma, RowBreak, Grp(),
            StrictSubset(oldScope, claimedScope),
            Sp, Rightarrow, Sp,
            Open, Forall, Sp, reading, Colon, Sp, readingType, Comma, Sp,
            Apply(deviation, reading, reading), Sp, Leq, Sp, epsilon, Close,
            Sp, Rightarrow, Sp,
            Open, Exists, Sp, ordinary, Comma, Sp, exceptional,
            Colon, Sp, readingType, Comma, Sp,
            epsilon, Sp, Lt, Sp, Apply(deviation, ordinary, exceptional), Close,
            Sp, Rightarrow, Sp,
            Exists, Sp, system, Comma, Sp, word, Colon, Sp, recordType, Comma, Sp,
            Call("EqOn", system, word, oldScope), Sp, Land, Sp,
            Call("WithinTolerance", deviation, epsilon, oldScope, system, word),
            Sp, Land, Sp, Neg,
            Call("WithinTolerance", deviation, epsilon, claimedScope, system, word));
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
