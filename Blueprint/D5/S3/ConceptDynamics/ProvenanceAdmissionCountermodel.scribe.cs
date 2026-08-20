using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics;

internal sealed class ProvenanceAdmissionCountermodelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equal report contents can carry provenance with opposite admission status.",
        H("Provenance-Sensitive Report Admission"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("equal-content-does-not-determine-admission"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/ProvenanceAdmissionCountermodel."
                        + "equal_content_does_not_determine_admission"),
                H("Equal content does not determine provenance-sensitive admission"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A provenance record contains the reported content together with checks for "
                            + "the data source, observation device, timestamp, reasoning procedure, "
                            + "intermediate proof, signature, dependency versions, and admission "
                            + "precondition. Validity requires content agreement and every check.")),
                    Paragraph(Text(
                        "The two concrete reports both contain the Boolean value false. Their "
                            + "provenance records differ only at the signature check: the first is "
                            + "verified and admitted, while the second is unverified and rejected.")),
                    Paragraph(Text(
                        "All six countermodel clauses are public, including the explicit failure of "
                            + "content equality to imply equal admission status. Admission is computed "
                            + "from the source evidence checks and is not defined from that failure.")),
                    Paragraph(Text(
                        "Repository and pinned-library searches found no canonical certified-report "
                            + "carrier or theorem to reuse. The exact Boolean inequality theorem is "
                            + "applied to the differing signature fields."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula TheoremFormula()
    {
        Formula first = Subscript(F.Id("r"), D(1));
        Formula second = Subscript(F.Id("r"), D(2));
        Formula reportType = Apply(
            Seq(Operatorname, Grp(F.Id("ProvenanceReport"))), F.Id("Bool"));
        Formula content = Seq(Operatorname, Grp(F.Id("content")));
        Formula provenance = Seq(Operatorname, Grp(F.Id("provenance")));
        Formula admission = Seq(Operatorname, Grp(F.Id("admitted")));
        Formula sameContent = Seq(
            Apply(content, first), Sp, Eq, Sp, Apply(content, second));
        Formula differentProvenance = Seq(
            Apply(provenance, first), Sp, Neq, Sp, Apply(provenance, second));
        Formula firstAdmitted = Apply(admission, first);
        Formula secondAdmitted = Apply(admission, second);
        Formula sameStatus = Seq(
            firstAdmitted, Sp, Iff, Sp, secondAdmitted);

        return Disp(Seq(
            Exists, Sp, first, Comma, Sp, second, Colon, Sp, reportType, Comma, Esc,
            sameContent, Sp, Land, RowBreak,
            differentProvenance, Sp, Land, RowBreak,
            firstAdmitted, Sp, Land, RowBreak,
            Neg, Sp, secondAdmitted, Sp, Land, RowBreak,
            Neg, Sp, Grp(sameStatus), Sp, Land, RowBreak,
            Neg, Sp, Open, sameContent, Sp, Rightarrow, Sp,
            Grp(sameStatus), Close, Dot));
    }

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));
}
