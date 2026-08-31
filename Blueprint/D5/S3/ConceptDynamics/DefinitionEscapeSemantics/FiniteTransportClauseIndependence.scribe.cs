using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscapeSemantics;

internal sealed class FiniteTransportClauseIndependenceDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/DefinitionEscapeSemantics/"
            + "FiniteTransportClauseIndependence.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Five constrained finite table models independently witness the necessity of the "
            + "five canonical transport-certificate clauses.",
        H("Finite Transport-Certificate Clause Independence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-transport-model"),
                DeclarationHandle.Create(Prefix + "FiniteTransportModel"),
                H("Constrained finite transport model"),
                StatementSource.FromAuthor(ModelFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The domain carrier has three points. Old and reported domains are Boolean "
                        + "characteristic tables; the receipt is exactly a content address, a "
                        + "domain table, and a version. Premises, transport assumptions, the "
                        + "partial prediction, acceptance, and claim truth are all finite "
                        + "Boolean tables. The structure contains no Prop-valued model field."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("transport-certificate-clause"),
                DeclarationHandle.Create(Prefix + "TransportCertificateClause"),
                H("Five certificate coordinates"),
                StatementSource.FromAuthor(ClauseFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The constructors follow the DECT 54.3 order: strict expansion, bound "
                        + "receipt, conditional transport, total prediction on the new-only "
                        + "domain, and a refuting failure witness."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-transport-certificate"),
                DeclarationHandle.Create(Prefix + "finiteTransportCertificate"),
                H("Certificate derived from finite tables"),
                StatementSource.FromAuthor(CertificateFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The two proposition fields of the frozen certificate carrier are not free: "
                        + "they are equality-to-true readings of the one-entry finite tables. "
                        + "Its prediction is the model's finite partial-function table."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-transport-frame"),
                DeclarationHandle.Create(Prefix + "finiteTransportFrame"),
                H("Semantic frame forced by finite tables"),
                StatementSource.FromAuthor(FrameFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Strict expansion and new-only membership are inherited from the frozen "
                            + "semantic frame and use characteristic-table membership.")),
                    Paragraph(Text(
                        "Receipt matching is exact equality of address, domain, and version. "
                            + "Definedness is membership in the graph of the partial prediction. "
                            + "Failure means that an observed result is rejected. Claim truth and "
                            + "refutation share one truth table, with refutation exactly result "
                            + "disagreement at the same point."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-transport-clause-holds"),
                DeclarationHandle.Create(Prefix + "finiteTransportClauseHolds"),
                H("Indexed canonical clause"),
                StatementSource.FromAuthor(ClauseHoldsFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Each index selects one top-level conjunct of the existing legacy "
                        + "ValidTransportCert after applying the frozen toLegacy map. It does not "
                        + "define a second certificate-validity predicate."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-transport-bad-report"),
                DeclarationHandle.Create(Prefix + "finiteTransportBadReport"),
                H("Independent finite bad-report reading"),
                StatementSource.FromAuthor(BadReportFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The five cases read raw finite data: an old point lost by the report, a "
                        + "mismatched receipt field, true premises with a false reported-domain "
                        + "claim, an undefined new-only point, or only accepted or truth-aligned "
                        + "defined outputs. Badness is not defined as clause negation."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-transport-clause-independence"),
                DeclarationHandle.Create(
                    Prefix + "finite_transport_certificate_clause_independence"),
                H("All five transport-certificate clauses are independently necessary"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The first conjunct checks clause fidelity: requiring every indexed "
                            + "coordinate is equivalent to the frozen canonical "
                            + "ValidTransportCert on every constrained finite model.")),
                    Paragraph(Text(
                        "The second conjunct supplies five separate three-point models. For each "
                            + "omitted coordinate all four retained coordinates hold, the omitted "
                            + "coordinate fails, and the corresponding independently defined bad "
                            + "report is present. The totality countermodel uses two new-only "
                            + "points so that one can be undefined while the other carries the "
                            + "required refuting failure witness.")),
                    Paragraph(Text(
                        "This closes OP4 from DECT part 55, atom "
                            + "generic-residual-38b77c703547818ccd62fb812de8f4084fc3f922b77676c15"
                            + "adff6a9624e1a0f, inside the constrained finite semantics class."))),
                DescribeRole.Theorem))));

    private static Formula ModelFormula() => Disp(Seq(
        F.Id("FiniteTransportModel"), Sp, Eq, Sp,
        Open,
        F.Id("J"), Comma, Sp,
        Seq(F.Id("J"), Apos), Comma, Sp,
        F.Id("claim"), Comma, Sp,
        F.Id("version"), Comma, Sp,
        F.Id("receipt"), Comma, Sp,
        F.Id("premiseTable"), Comma, Sp,
        F.Id("transportTable"), Comma, RowBreak, Grp(),
        F.Id("predictionTable"), Comma, Sp,
        F.Id("acceptanceTable"), Comma, Sp,
        F.Id("truthTable"),
        Close, Dot));

    private static Formula ClauseFormula() => Disp(Seq(
        F.Id("TransportCertificateClause"), Sp, Eq, Sp,
        OpenBrace,
        F.Id("strictExpansion"), Comma, Sp,
        F.Id("receiptBound"), Comma, Sp,
        F.Id("conditionalTransport"), Comma, RowBreak, Grp(),
        F.Id("totalOnNewOnly"), Comma, Sp,
        F.Id("refutingFailure"),
        CloseBrace, Dot));

    private static Formula CertificateFormula()
    {
        Formula model = F.Id("M");
        return Disp(Seq(
            Call("finiteTransportCertificate", model), Colon, Sp,
            F.Id("TransportCert"), Dot));
    }

    private static Formula FrameFormula()
    {
        Formula model = F.Id("M");
        return Disp(Seq(
            Call("finiteTransportFrame", model), Colon, Sp,
            F.Id("TransportSemanticFrame"), Dot));
    }

    private static Formula ClauseHoldsFormula()
    {
        Formula model = F.Id("M");
        Formula clause = Seq(F.Id("C"), Underscore, F.Id("j"));
        return Disp(Seq(
            Call("finiteTransportClauseHolds", model, clause), Sp, Eq, Sp,
            Call("C", clause, model), Dot));
    }

    private static Formula BadReportFormula()
    {
        Formula model = F.Id("M");
        Formula clause = Seq(F.Id("C"), Underscore, F.Id("j"));
        return Disp(Seq(
            Call("finiteTransportBadReport", model, clause), Sp, Eq, Sp,
            Call("Bad", clause, model), Dot));
    }

    private static Formula Holds(Formula model, Formula clause) =>
        Call("finiteTransportClauseHolds", model, clause);

    private static Formula Bad(Formula model, Formula clause) =>
        Call("finiteTransportBadReport", model, clause);

    private static Formula Field(Formula model, string field) =>
        Seq(model, Dot, F.Id(field));

    private static Formula CanonicalValidity(Formula model) => Call(
        "ValidTransportCert",
        Seq(Call("finiteTransportFrame", model), Dot, F.Id("toLegacy")),
        Call("finiteTransportCertificate", model),
        Field(model, "claim"),
        Field(model, "oldDomain"),
        Field(model, "reportedDomain"),
        Field(model, "version"));

    private static Formula TheoremFormula()
    {
        Formula model = F.Id("M");
        Formula witnessModel = Seq(F.Id("M"), Underscore, F.Id("j"));
        Formula clause = F.Id("C");
        Formula omitted = Seq(F.Id("C"), Underscore, F.Id("j"));
        Formula retained = Seq(F.Id("C"), Underscore, F.Id("k"));
        Formula modelType = F.Id("FiniteTransportModel");
        Formula clauseType = F.Id("TransportCertificateClause");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Open,
            Forall, Sp, model, Colon, Sp, modelType, Comma, RowBreak, Grp(),
            Open, Forall, Sp, clause, Colon, Sp, clauseType, Comma, Sp,
            Holds(model, clause), Close,
            Sp, Iff, Sp, CanonicalValidity(model),
            Close, RowBreak, Grp(),
            Land, RowBreak, Grp(),
            Forall, Sp, omitted, Colon, Sp, clauseType, Comma, Sp,
            Exists, Sp, witnessModel, Colon, Sp, modelType, Comma, RowBreak, Grp(),
            Open,
            Forall, Sp, retained, Colon, Sp, clauseType, Comma, Sp,
            retained, Sp, Neq, Sp, omitted, Sp, Rightarrow, Sp,
            Holds(witnessModel, retained),
            Close, Sp, Land, RowBreak, Grp(),
            Neg, Holds(witnessModel, omitted), Sp, Land, Sp,
            Bad(witnessModel, omitted), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
