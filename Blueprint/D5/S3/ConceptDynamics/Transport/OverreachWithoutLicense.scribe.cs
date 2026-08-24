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
                        "A transport report stores its concept c, its claimed operation scope "
                            + "J', and its retained proposition Gamma. LicensedReport also checks "
                            + "that the stored scope equals the explicit J', so the target domain "
                            + "cannot drift through a free argument.")),
                    Paragraph(Text(
                        "ValidTransportCert is an abstract predicate parameter here. Its arguments "
                            + "are the certificate, c, the old and claimed scopes, and Version(c). "
                            + "The separate certificate-validity module owns that predicate and "
                            + "can be connected without creating a second validity definition.")),
                    Paragraph(Text(
                        "A license retains Gamma exactly as GivenPremises(kappa) conjoined with the "
                            + "certificate's transport assumption. Therefore an unconditional "
                            + "licensed report exposes proofs of both conjuncts, while a missing "
                            + "conjunct prevents the condition from being discharged.")),
                    Paragraph(Text(
                        "Overreach is the conjunction of strict scope expansion, Scope(c)=J, the "
                            + "report's claim of J', and absence of a license. No certificate "
                            + "validity or premise is inferred from the scope equations.")),
                    Paragraph(Text(
                        "For a strict expansion, a new operation is selected with Mathlib's "
                            + "ssubset witness. If unchanged readings remain within epsilon and "
                            + "the reading space admits an above-epsilon deviation, two records "
                            + "agree and fit on J but fail on J'.")),
                    Paragraph(Text(
                        "Local completion uses the canonical restricted equality Set.EqOn. Two "
                            + "distinct readings at the selected new operation give Closed_J(S,T) "
                            + "and not Closed_J'(S,T), so expansion reopens local completion.")),
                    Paragraph(Text(
                        "Conversely, a valid certificate together with every given premise and its "
                            + "transport assumption licenses the report whose retained condition is "
                            + "True. Without those proofs, the exact conditional statement remains "
                            + "the only licensed form.")),
                    Paragraph(Text(
                        "Repository type-shape, English and Chinese synonym, and neighboring-module "
                            + "searches found no transport-license or overreach definition. "
                            + "Concept and Set.EqOn are reused; the canonical defectRelation remains "
                            + "untouched because no escape-residual relation is needed here."))),
                DescribeRole.Theorem))));

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula TheoremFormula()
    {
        Formula q = F.Id("q");
        Formula c = F.Id("c");
        Formula oldScope = F.Id("J");
        Formula claimedScope = Seq(F.Id("J"), Apos);
        Formula certificate = Kappa;
        Formula gammaQ = Subscript(Gamma, q);
        Formula licensed = Call("LicensedReport", q, oldScope, claimedScope);
        Formula validCertificate = Call(
            "ValidTransportCert",
            certificate,
            c,
            oldScope,
            claimedScope,
            Call("Version", c));
        Formula premises = Call("GivenPremises", certificate);
        Formula assumption = Call("TransportAssumption", certificate);
        Formula completeCondition = Grp(
            gammaQ, Sp, Iff, Sp, premises, Sp, Land, Sp, assumption);
        Formula reportScope = Call("reportedScope", q);
        Formula licenseDefinition = Grp(
            licensed, Sp, Iff, Sp,
            reportScope, Sp, Eq, Sp, claimedScope, Sp, Land, Sp,
            Exists, Sp, certificate, Comma, Sp,
            validCertificate, Sp, Land, Sp, completeCondition);
        Formula unconditionalDuty = Grp(
            gammaQ, Sp, Eq, Sp, F.Id("top"), Sp, Land, Sp, licensed,
            Sp, Rightarrow, Sp,
            Exists, Sp, certificate, Comma, Sp,
            validCertificate, Sp, Land, Sp, premises, Sp, Land, Sp, assumption);
        Formula retainedCondition = Grp(
            licensed, Sp, Rightarrow, Sp,
            Exists, Sp, certificate, Comma, Sp,
            validCertificate, Sp, Land, Sp, completeCondition, Sp, Land, Sp,
            Open, Open, Neg, premises, Sp, Lor, Sp, Neg, assumption, Close,
            Sp, Rightarrow, Sp, Neg, gammaQ, Close);
        Formula overreachDefinition = Grp(
            Call("Overreach", q, oldScope, claimedScope), Sp, Iff, Sp,
            oldScope, Sp, Subset, Sp, claimedScope, Sp, Land, Sp,
            Call("Scope", c), Sp, Eq, Sp, oldScope, Sp, Land, Sp,
            reportScope, Sp, Eq, Sp, claimedScope, Sp, Land, Sp,
            Neg, licensed);
        Formula toleranceCounterexample = ToleranceCounterexample(oldScope, claimedScope);
        Formula closureCounterexample = ClosureCounterexample(oldScope, claimedScope);
        Formula deconditioning = Grp(
            validCertificate, Sp, Land, Sp, premises, Sp, Land, Sp, assumption,
            Sp, Rightarrow, Sp,
            Call("LicensedReport", Subscript(q, F.Id("top")), oldScope, claimedScope));

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

    private static Formula ToleranceCounterexample(
        Formula oldScope,
        Formula claimedScope)
    {
        Formula deviation = DeltaLower;
        Formula epsilon = Varepsilon;
        Formula reading = F.Id("r");
        Formula ordinary = F.Id("a");
        Formula exceptional = F.Id("b");
        Formula system = F.Id("S");
        Formula word = F.Id("w");

        return Grp(
            oldScope, Sp, Subset, Sp, claimedScope, Sp, Land, Sp,
            Open, Forall, Sp, reading, Comma, Sp,
            Call("delta", reading, reading), Sp, Leq, Sp, epsilon, Close,
            Sp, Land, Sp,
            Open, Exists, Sp, ordinary, Comma, Sp, exceptional, Comma, Sp,
            epsilon, Sp, Lt, Sp, Call("delta", ordinary, exceptional), Close,
            Sp, Rightarrow, Sp,
            Exists, Sp, system, Comma, Sp, word, Comma, Sp,
            Call("EqOn", system, word, oldScope), Sp, Land, Sp,
            Call("WithinTolerance", deviation, epsilon, oldScope, system, word),
            Sp, Land, Sp, Neg,
            Call("WithinTolerance", deviation, epsilon, claimedScope, system, word));
    }

    private static Formula ClosureCounterexample(
        Formula oldScope,
        Formula claimedScope)
    {
        Formula ordinary = F.Id("a");
        Formula exceptional = F.Id("b");
        Formula system = F.Id("S");
        Formula target = F.Id("T");

        return Grp(
            oldScope, Sp, Subset, Sp, claimedScope, Sp, Land, Sp,
            Open, Exists, Sp, ordinary, Comma, Sp, exceptional, Comma, Sp,
            ordinary, Sp, Neq, Sp, exceptional, Close,
            Sp, Rightarrow, Sp,
            Exists, Sp, system, Comma, Sp, target, Comma, Sp,
            Call("LocallyClosed", oldScope, system, target), Sp, Land, Sp,
            Neg, Call("LocallyClosed", claimedScope, system, target));
    }
}
