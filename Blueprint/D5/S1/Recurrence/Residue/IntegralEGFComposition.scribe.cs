using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Residue;

internal sealed class IntegralEGFCompositionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Residue/IntegralEGFComposition.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Factorial-normalized rational coefficients compose by an integral chain-rule recurrence.",
        H("Integral EGF Composition"),
        Blocks(
            Paragraph(Text("For a rational formal power series f, eCoeff(f,n) means "
                + "n! times its ordinary coefficient. All indices are natural numbers. "
                + "Composition below uses an inner series with constant coefficient zero; "
                + "this condition is proved at every use in the A396804 construction.")),
            Note("eCoeff", "Factorial normalization",
                "The coefficient eCoeff(f,n) is defined in Rat, without any integrality assumption."),
            Note("eCoeff_mul", "Binomial multiplication",
                "The ordinary Cauchy product becomes the sum of binomial(n,i) times "
                + "eCoeff(f,i) times eCoeff(g,n-i). The factorial identity in Mathlib "
                + "justifies the conversion."),
            Note("composition", "Integral composition recurrence",
                "C(f,g)(0)=f(0). At n+1, sum binomial(n,i) C(shift(f),g)(i) "
                + "g(n-i+1) over 0<=i<=n. This well-founded recurrence makes sense "
                + "over every commutative semiring and implicitly uses inner constant zero."),
            Note("eCoeff_composition", "Agreement with rational substitution",
                "The formal chain rule and binomial multiplication prove that the recurrence "
                + "computes exactly eCoeff(f composed with g). This is an all-degree theorem "
                + "with the explicit hypothesis constantCoeff(g)=0."),
            Note("composition_map", "Coefficient reduction",
                "Applying any semiring homomorphism before or after the integral recurrence "
                + "has the same result. This supplies reduction modulo two and four."),
            Note("composition_congr", "Dependence on the finite prefix",
                "The degree-n result depends only on outer and inner coefficients through n. "
                + "Strong induction proves this locality statement."),
            Note("natural_subst", "Natural integrality",
                "Natural EGF coefficients remain natural under valid substitution. The proof "
                + "uses the natural-valued recurrence and its rational interpretation."),
            Note("integral_subst", "Signed integrality",
                "The same argument over Int permits subtraction and the integral half-series "
                + "needed by the modulo-four lifting argument."))));

    private static DocumentBlock Note(string name, string title, string prose) =>
        Describe.Remark(DescribeId.Create("integral-egf-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))));
}
