using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms.CrossingCertificates;

internal sealed class BoundedWindingPhaseZeroCertificateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula matrix = F.Id("A");
        Formula phaseValue = F.Id("z");
        Formula modulus = F.Id("M");
        Formula phase = Seq(Operatorname, Grp(F.Id("windingPhase")), Open, matrix, Close);
        Formula statement = Disp(Seq(
            Forall, Sp, matrix, Colon, Sp,
            Operatorname, Grp(F.Id("PositiveMatrix")), Comma, Sp,
            phaseValue, InMacro, Sp, Mathbb, Grp(F.Id("Z")), Comma, Sp,
            modulus, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma,
            RowBreak, Grp(), phase, Sp, Eq, Sp, phaseValue, Sp, Land, Sp,
            new Formula.Absolute(phaseValue), Sp, Lt, Sp, modulus, Sp, Land, Sp,
            modulus, Sp, Mid, Sp, phaseValue, Sp, Rightarrow, Sp,
            phase, Sp, Eq, Sp, D(0), Dot));

        return DocumentDefinition.Create(ScribeNode.Create(
            "A finite local zero certificate becomes global under a strict phase bound.",
            H("Bounded Winding Phase Zero Certificate"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("bounded-winding-phase-zero-certificate"),
                    DeclarationHandle.Create(
                        "D5/S3/PrimeForms/CrossingCertificates/"
                            + "BoundedWindingPhaseZeroCertificate."
                            + "bounded_winding_phase_zero_certificate"),
                    H("A bounded divisible winding phase is zero"),
                    StatementSource.FromAuthor(statement),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Let A be the repository's canonical positive matrix and let its "
                                + "rational winding phase equal the integer z. The public "
                                + "integrality equation bridges the actual phase carrier to the "
                                + "integer divisibility assertion.")),
                        Paragraph(Text(
                            "If the absolute value of z is strictly below the natural modulus M "
                                + "and M divides z, the exact integer bounded-divisibility theorem "
                                + "forces z to vanish. Substitution through the public phase "
                                + "equation gives windingPhase(A) = 0.")),
                        Paragraph(Text(
                            "The proof directly applies the pinned-library theorem "
                                + "Int.eq_zero_of_abs_lt_dvd. Repository searches found and reused "
                                + "PositiveMatrix and windingPhase from the crossing family; no "
                                + "new phase carrier or channel is introduced."))),
                    DescribeRole.Theorem))));
    }
}
