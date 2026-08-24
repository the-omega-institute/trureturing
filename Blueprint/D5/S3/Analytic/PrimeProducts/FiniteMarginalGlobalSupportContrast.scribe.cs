using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.PrimeProducts;

internal sealed class FiniteMarginalGlobalSupportContrastDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compatible finite geometric prime-exponent laws coexist with a product law "
            + "that almost surely has infinitely many active coordinates.",
        H("Finite Prime Marginals and Global Support"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-marginals-global-support-contrast"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/PrimeProducts/FiniteMarginalGlobalSupportContrast."
                        + "finite_marginals_and_global_support_contrast"),
                H("Finite marginals are compatible while finite global support is null"),
                StatementSource.FromAuthor(ContrastFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every positive real s and prime p, the activation probability "
                            + "is p to the power minus s. The coordinate law is constructed "
                            + "as the zero-start geometric measure with success parameter "
                            + "one minus that activation probability, and the global law is "
                            + "Mathlib's canonical infinite product of these coordinates.")),
                    Paragraph(Text(
                        "Every finite coordinate product is a probability measure. Restricting "
                            + "the global product to any finite prime set gives exactly that "
                            + "finite product, and every finite cylinder has the displayed "
                            + "product of geometric singleton masses.")),
                    Paragraph(Text(
                        "When s is at most one, the prime activation masses have divergent "
                            + "sum. Product-coordinate independence and the second Borel-Cantelli "
                            + "lemma therefore give infinitely many active primes almost surely, "
                            + "so the set of finite-support exponent profiles has measure zero."))),
                DescribeRole.Theorem))));

    private static Formula ContrastFormula()
    {
        Formula s = F.Id("s");
        Formula p = F.Id("p");
        Formula finiteSet = F.Id("S");
        Formula exponents = F.Id("e");
        Formula primeSet = Seq(Mathbb, Grp(F.Id("P")));
        Formula q = Seq(F.Id("q"), Underscore, Grp(p, Comma, s));
        Formula localLaw = Seq(GammaLower, Underscore, Grp(p, Comma, s));
        Formula globalLaw = Seq(Gamma, Underscore, Grp(s));
        Formula pToMinusS = Seq(p, Caret, Grp(Minus, s));
        Formula exponentAtP = Seq(exponents, Underscore, Grp(p));
        Formula localMass = Seq(
            Open, D(1), Minus, pToMinusS, Close,
            p, Caret, Grp(Minus, s, exponentAtP));
        Formula cylinder = Call("Cylinder", finiteSet, exponents);
        Formula finiteProduct = Seq(
            Prod, Underscore, Grp(p, InMacro, Sp, finiteSet), Sp, localMass);

        return Disp(new Formula.Aligned([
            Seq(
                D(0), Lt, s, Leq, D(1), Comma, Sp,
                q, Eq, pToMinusS, Comma, Sp,
                localLaw, Eq, Call("geometricMeasure", Seq(D(1), Minus, q)), Comma, Sp,
                globalLaw, Eq, Call("infinitePi", localLaw)),
            Seq(
                Forall, Sp, finiteSet, Subset, Underscore, Grp(Operatorname,
                    Grp(F.Id("fin"))), primeSet, Comma, Sp,
                Call("ProbabilityMeasure", Call("finiteProduct", finiteSet, localLaw)),
                Sp, Land, Sp,
                Call("map", Call("restrict", finiteSet), globalLaw), Eq,
                Call("finiteProduct", finiteSet, localLaw)),
            Seq(
                Forall, Sp, finiteSet, Comma, Sp, exponents, Comma, Sp,
                Call("Pr", globalLaw, cylinder), Eq, finiteProduct),
            Seq(
                Call("Pr", globalLaw, F.Id("FiniteSupportProfiles")), Eq, D(0), Dot),
        ]));
    }
}
