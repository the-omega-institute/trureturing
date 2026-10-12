using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.NumberTheory.ModularForms;

internal sealed class ActualPrimeHeckeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual prime Hecke endomorphism, its complete finite representatives, and its analytic coefficient law.",
        H("Actual Prime Hecke Action"),
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
                DescribeId.Create("prime-hecke-literal-action"),
                DeclarationHandle.Create(
                    "D5/S1/NumberTheory/ModularForms/ActualPrimeHecke.primeHecke_action"),
                H("The full p+1 action"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("primeHeckeAction"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every prime p, including 2, every integer weight k and every upper-half-plane point z, the actual trace equals p^(k-1) times f(pz) plus p^(-1) times the sum of f((z+a)/p) over a in Fin p. Both points have explicit positivity proofs. Mathlib uses inverse representatives: 1 and (S T^a)^(-1). The actual slash normalization gives these factors without any weight restriction.")),
                    Paragraph(Text(
                    "The representative map primeTraceEquiv is a proved bijection from Fin p plus Unit onto the actual quotient in the trace. Its coverage and uniqueness are consumed by the trace reindexing."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-hecke-congruence-intersection"),
                DeclarationHandle.Create(
                    "D5/S1/NumberTheory/ModularForms/ActualPrimeHecke.primeHeckeSubgroup_mem"),
                H("The actual congruence intersection"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("primeHeckeSubgroupMem"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For an integer determinant-one matrix s, its real image belongs to the conjugate by diag(p,1)^(-1) of SL2(Z) exactly when its lower-left entry is divisible by p. This identifies the actual trace intersection with Gamma0(p). Coverage and uniqueness of the representatives are proved from this entry criterion, using ZMod p as a field; no representative frame is assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-hecke-analytic-coefficients"),
                DeclarationHandle.Create(
                    "D5/S1/NumberTheory/ModularForms/ActualPrimeHecke.primeHecke_qExpansion_coeff"),
                H("The analytic coefficient law"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("primeHeckeQExpansionCoeff"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Writing a(f,n) for coefficient n of the period-one analytic q-expansion, a(T_p f,n) = a(f,p*n) + p^(k-1) * (if p divides n then a(f,n/p) else 0). The theorem quantifies over every prime, every integer weight, every level-one cusp form and every natural coefficient index, including zero.")),
                    Paragraph(Text(
                    "The proof uses Mathlib's HasSum theorem for the actual function at pz and at each (z+a)/p. The finite root-of-unity filter removes the nonmultiples of p. Finite sums of HasSum and injective integer-multiple reindexing preserve convergence; analytic coefficient uniqueness identifies the resulting coefficients. No formal-series recurrence or coefficient formula is a premise.")),
                    Paragraph(Text(
                    "The classical normalization is the one in Ribet and Stein, Lectures on Modular Forms and Hecke Operators, section 3.5.2 and Proposition 3.5.2. This is a reusable analytic library construction. It does not resolve Lehmer's conjecture; the coefficient relation allows a vanishing prime coefficient. The module remains unfrozen pending independent review. A complete four-slot source registration is not asserted."))),
                DescribeRole.Theorem))));
}
