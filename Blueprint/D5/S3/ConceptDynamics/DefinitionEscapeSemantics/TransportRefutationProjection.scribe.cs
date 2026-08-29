using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscapeSemantics;

internal sealed class TransportRefutationProjectionDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/DefinitionEscapeSemantics/"
            + "TransportRefutationProjection."
            + "transport_refutation_witness_projects_to_prop";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A typed transport refutation witness exposes its same-run propositional consequences.",
        H("Typed Transport-Refutation Projection"),
        Blocks(Describe.Lean(
            DescribeId.Create("typed-transport-refutation-projection"),
            DeclarationHandle.Create(Declaration),
            H("A typed refutation witness projects to four propositions"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The semantic frame interprets the prediction registered by the frozen "
                        + "transport-certificate carrier. The witness stores one point, one "
                        + "returned result, failure of that result, and refutation of the same "
                        + "claim by the same result.")),
                Paragraph(Text(
                    "The conclusion exposes new-domain membership, prediction definedness, "
                        + "prediction failure, and claim refutation at that one point. Each "
                        + "run-dependent conjunct is constructed from the witness's stored "
                        + "result; no result equality or decidability assumption is used.")),
                Paragraph(Text(
                    "This discharges obligation 57.3-B from definition-escape-completion-theory "
                        + "atom generic-residual-ec58c77abc2d1b2b22f690f3a3d268dcc2ff353d26dd2"
                        + "f317c0da0845820b8e0."))),
            DescribeRole.Theorem))));

    private static Formula Parenthesize(Formula formula) =>
        Seq(Open, formula, Close);

    private static Formula TheoremFormula()
    {
        Formula frame = F.Id("S");
        Formula certificate = F.Id("cert");
        Formula claim = F.Id("claim");
        Formula oldDomain = F.Id("J");
        Formula newDomain = Seq(F.Id("J"), Apos);
        Formula witness = F.Id("w");
        Formula evidence = F.Id("z");
        Formula prediction = Seq(certificate, Dot, F.Id("falsifiablePrediction"));
        Formula witnessType = Call(
            "TransportRefutationWitness",
            frame,
            certificate,
            claim,
            oldDomain,
            newDomain);
        Formula newOnly = Call(
            "SemanticNewOnly", frame, evidence, oldDomain, newDomain);
        Formula defined = Call(
            "SemanticPredictionDefined", frame, prediction, evidence);
        Formula fails = Call(
            "SemanticPredictionFails", frame, prediction, evidence);
        Formula refutes = Call(
            "SemanticRefutes", frame, evidence, certificate, claim);

        return Disp(Seq(
            Forall, Sp, witness, Sp, Colon, Sp, witnessType, Comma, Sp,
            Exists, Sp, evidence, Comma, Sp,
            newOnly, Sp, Land, RowBreak, Grp(),
            Parenthesize(defined), Sp, Land, RowBreak, Grp(),
            Parenthesize(fails), Sp, Land, RowBreak, Grp(),
            Parenthesize(refutes), Dot));
    }
}
