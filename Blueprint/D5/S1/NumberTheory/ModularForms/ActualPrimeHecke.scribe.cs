using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.NumberTheory.ModularForms;

internal sealed class ActualPrimeHeckeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An actual trace-and-translate prime Hecke endomorphism on level-one cusp forms.",
        H("Actual Prime Hecke Trace"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-hecke-endomorphism"),
                DeclarationHandle.Create(
                    "D5/S1/NumberTheory/ModularForms/ActualPrimeHecke.primeHecke"),
                H("Actual prime Hecke endomorphism"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("primeHecke")), Sp,
                    Colon, Sp, F.Id("CuspForm"), Sp, Rightarrow, Sp,
                    F.Id("CuspForm")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a prime p and an integer weight k, this is the complex-linear map obtained by translating by the rational diagonal p-isogeny matrix and applying Mathlib's finite-index cusp-form trace. The codomain is the level-one CuspForm space itself; the trace construction supplies holomorphy and vanishing at every cusp."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-hecke-trace-application"),
                DeclarationHandle.Create(
                    "D5/S1/NumberTheory/ModularForms/ActualPrimeHecke.primeHecke_apply"),
                H("Pointwise trace application"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("primeHeckeApply"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The pointwise equality unfolds the endomorphism to the actual translated cusp-form trace. The finite quotient and its inverse representative convention remain explicit in the library definition.")),
                    Paragraph(Text(
                    "The explicit P^1(F_p) representative expansion, the literal upper-triangular slash formula, and the unconditional convergent q-expansion coefficient law are not asserted by this document; they remain the next unpaid obligations for the complete analytic unit."))),
                DescribeRole.Theorem))));
}
