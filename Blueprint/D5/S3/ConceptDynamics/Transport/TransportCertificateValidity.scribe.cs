using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Transport;

internal sealed class TransportCertificateValidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Valid transport certificates need locked receipts and nonempty failures.",
        H("Transport-Certificate Validity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("valid-transport-cert-criterion"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Transport/TransportCertificateValidity."
                        + "valid_transport_cert_criterion"),
                H("The four claim-bound validity clauses"),
                StatementSource.FromAuthor(CriterionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A transport certificate is the triple consisting of a source receipt, "
                            + "an explicit transport assumption, and a falsifiable prediction. "
                            + "The prediction type itself requires a nonempty failure event in "
                            + "the target-minus-source domain, so constant-false failure data "
                            + "cannot be packaged as a certificate.")),
                    Paragraph(Text(
                        "Receipt matching identifies the receipt's original record with the "
                            + "record actually supplied to transport, then binds its source "
                            + "domain, version, error, and transported claim content address. "
                            + "The transport candidate returns a claim whose declared target "
                            + "scope is a type index, without carrying a ClaimOn proof. The "
                            + "second clause "
                            + "is conditional: the given premises together with every declared "
                            + "preservation obligation imply that the same claim holds on the "
                            + "target domain.")),
                    Paragraph(Text(
                        "Selection mechanisms, intervention consistency, covariate "
                            + "transformations, and loss stability each have an explicit "
                            + "dependency flag and preservation obligation in the transport "
                            + "assumption. None is hidden behind an undifferentiated similarity "
                            + "premise.")),
                    Paragraph(Text(
                        "The last two conjuncts require preregistration over the entire new-domain "
                            + "difference and a concrete point where the prediction is defined, "
                            + "fails, and refutes this certificate's transported claim. The "
                            + "existential closure HasValidTransportCert takes the source record, "
                            + "fixes the version to Version(c), and calls this same predicate, "
                            + "with no Boolean gate.")),
                    Paragraph(Text(
                        "This formalizes definition-escape-completion-theory atom "
                            + "generic-residual-1e2a241367ada0b7e8670ff4fdba1b0b420500208eb803"
                            + "69635bd5c9bfdb2ff3."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Predicate(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);

    private static Formula Parenthesize(Formula formula) =>
        Seq(Open, formula, Close);

    private static Formula CriterionFormula()
    {
        Formula claim = F.Id("c");
        Formula record = F.Id("r");
        Formula source = F.Id("J");
        Formula target = F.Id("Jprime");
        Formula version = F.Id("nu");
        Formula point = F.Id("z");
        Formula receipt = Seq(Kappa, Dot, F.Id("Receipt"));
        Formula assumption = Seq(Kappa, Dot, F.Id("TransportAssumption"));
        Formula difference = Seq(target, Sp, Setminus, Sp, source);
        Formula valid = Predicate(
            "ValidTransportCert", Kappa, record, claim, source, target, version);
        Formula receiptMatch = Predicate(
            "ReceiptMatches", receipt, record, Predicate("ClaimAddress", claim), source, version);
        Formula conditionalTransport = Seq(
            Open,
            Predicate("GivenPremises", Kappa), Sp, Land, Sp,
            Predicate("Holds", assumption),
            Close, Sp, Rightarrow, Sp,
            Predicate("ClaimOn", claim, target));
        Formula coverage = Seq(
            Forall, Sp, point, Sp, InMacro, Sp, difference, Comma, Sp,
            Predicate("PredictionDefined", Kappa, point));
        Formula witness = Seq(
            Exists, Sp, point, Sp, InMacro, Sp, difference, Comma, Sp,
            Predicate("PredictionDefined", Kappa, point), Sp, Land, Sp,
            Predicate("PredictionFails", Kappa, point), Sp, Land, Sp,
            Predicate("Refutes", point, Kappa, claim));

        return Disp(Seq(
            valid, Sp, Iff, Sp,
            receiptMatch, Sp, Land, RowBreak, Grp(),
            Parenthesize(conditionalTransport), Sp, Land, RowBreak, Grp(),
            Parenthesize(coverage), Sp, Land, RowBreak, Grp(),
            Parenthesize(witness), Dot));
    }
}
