using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.ModularForms;

internal sealed class ActualPrimeHeckeDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Fourier/ribetstein2017modularforms");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual prime Hecke endomorphism, its complete finite representatives, and its analytic coefficient law.",
        H("Actual Prime Hecke Action"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-hecke-endomorphism"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/ModularForms/ActualPrimeHecke.primeHecke"),
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
                    "D5/S3/Arith/ModularForms/ActualPrimeHecke.primeHecke_action"),
                H("The full p+1 action"),
                StatementSource.FromAuthor(ActionFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every prime p, including 2, every integer weight k and every upper-half-plane point z, the actual trace equals p^(k-1) times f(pz) plus p^(-1) times the sum of f((z+a)/p) over a in Fin p. Both points have explicit positivity proofs. Mathlib uses inverse representatives: 1 and (S T^a)^(-1). The actual slash normalization gives these factors without any weight restriction.")),
                    Paragraph(Text(
                    "The representative map primeTraceEquiv is a proved bijection from Fin p plus Unit onto the actual quotient in the trace. Its coverage and uniqueness are consumed by the trace reindexing.")),
                    Paragraph(Text(
                    "Ribet and Stein, Lectures on Modular Forms and Hecke Operators, January 12, 2017 version, Proposition 3.5.2, printed p. 20, classifies the triangular representatives. Section 3.5.2, printed pp. 21–22, derives the n^(k-1) d^(-k) normalization and this prime action. The inverse-representative quotient bijection and its Mathlib trace realization are repository implementations of that classical action."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-hecke-congruence-intersection"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/ModularForms/ActualPrimeHecke.primeHeckeSubgroup_mem"),
                H("The actual congruence intersection"),
                StatementSource.FromAuthor(IntersectionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For an integer determinant-one matrix s, its real image belongs to the conjugate by diag(p,1)^(-1) of SL2(Z) exactly when its lower-left entry is divisible by p. This identifies the actual trace intersection with Gamma0(p). Coverage and uniqueness of the representatives are proved from this entry criterion, using ZMod p as a field; no representative frame is assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-hecke-analytic-coefficients"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/ModularForms/ActualPrimeHecke.primeHecke_qExpansion_coeff"),
                H("The analytic coefficient law"),
                StatementSource.FromAuthor(CoefficientFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Writing a(f,n) for coefficient n of the period-one analytic q-expansion, a(T_p f,n) = a(f,p*n) + p^(k-1) * (if p divides n then a(f,n/p) else 0). The theorem quantifies over every prime, every integer weight, every level-one cusp form and every natural coefficient index, including zero.")),
                    Paragraph(Text(
                    "The proof uses Mathlib's HasSum theorem for the actual function at pz and at each (z+a)/p. The finite root-of-unity filter removes the nonmultiples of p. Finite sums of HasSum and injective integer-multiple reindexing preserve convergence; analytic coefficient uniqueness identifies the resulting coefficients. No formal-series recurrence or coefficient formula is a premise.")),
                    Paragraph(Text(
                    "Ribet and Stein, Lectures on Modular Forms and Hecke Operators, January 12, 2017 version, section 3.5.2, printed pp. 21–22, derives this normalized prime coefficient law, including the constant coefficient. Proposition 3.5.2, printed p. 20, classifies representatives; it is not itself the coefficient theorem. The convergence and coefficient-uniqueness bridges are repository proofs using Mathlib. This is a reusable analytic library construction. It does not resolve Lehmer's conjecture; the coefficient relation allows a vanishing prime coefficient.")),
                    Paragraph(Text(
                    "The four-slot escape audit is unfinished under the existing owner issue https://github.com/the-omega-institute/trureturing/issues/5214 (escape registration current interfaces). No declared_validated registration is claimed. Reg.Support.DependentFamily.enrollment_1 supplies a generic enrolled template, not a source registration of these Hecke statements.")),
                    Paragraph(Text(
                    "For primeHecke_action, the missing evidence is whole-family role sensitivity, nonconstant actual analytic observation in each role, and a typed Contract.Registration with checked source-selection reconstruction. For primeHecke_qExpansion_coeff, it is whole-family role sensitivity, nonconstant actual coefficient observation in each role, and the same typed source-selection bridge. For primeHeckeSubgroup_mem, whole-family law variation, role sensitivity, actual observational dependence, and the typed Contract.Registration source-selection bridge remain unfinished.")),
                    Paragraph(Text(
                    "The audit must retain every prime including 2, every integer weight, all level-one cusp forms and upper-half-plane points, and every natural coefficient index including 0. Weight and coefficient-index degeneracies remain in scope; no sensitivity at each fixed weight or index is asserted. The missing evidence establishes neither absence of a suitable template nor a mathematical failure of the Hecke laws."))),
                DescribeRole.Theorem))));

    private static Formula ActionFormula()
    {
        Formula p = F.Id("p"), k = F.Id("k"), f = F.Id("f");
        Formula z = F.Id("z"), a = F.Id("a");
        Formula tp = new Formula.Subscript(F.Id("T"), p);
        Formula factor = new Formula.Power(p, Subtract(k, D(1)));
        Formula index = Seq(a, Sp, InMacro, Sp, Call("Fin", p));
        Formula sum = Seq(Sum, Underscore, Grp(index), Sp,
            Call("f", new Formula.Fraction(Add(z, a), p)));
        return Disp(Seq(Open, tp, Sp, f, Close, Open, z, Close, Sp, Eq, Sp,
            Multiply(factor, Call("f", Multiply(p, z))), Sp, Plus, Sp,
            Multiply(new Formula.Fraction(D(1), p), sum)));
    }

    private static Formula IntersectionFormula()
    {
        Formula p = F.Id("p"), s = F.Id("s");
        Formula gamma = new Formula.Subscript(Gamma, D(0));
        return Disp(Seq(Call("mapGL", s), Sp, InMacro, Sp,
            Call("primeHeckeSubgroup", p), Sp, Leftrightarrow, Sp,
            s, Sp, InMacro, Sp, gamma, Open, p, Close));
    }

    private static Formula CoefficientFormula()
    {
        Formula p = F.Id("p"), k = F.Id("k"), f = F.Id("f"), n = F.Id("n");
        Formula tp = new Formula.Subscript(F.Id("T"), p);
        Formula condition = new Formula.Relation(p, FormulaRelationOperator.Divides, n);
        Formula selected = Seq(Open,
            F.Text, Grp(F.Id("if")), Sp, condition, Sp,
            F.Text, Grp(F.Id("then")), Sp,
            Call("a", f, new Formula.Floor(new Formula.Fraction(n, p))), Sp,
            F.Text, Grp(F.Id("else")), Sp, D(0), Close);
        return Disp(Equal(Call("a", Seq(tp, Sp, f), n),
            Add(Call("a", f, Multiply(p, n)),
                Multiply(new Formula.Power(p, Subtract(k, D(1))), selected))));
    }
}
