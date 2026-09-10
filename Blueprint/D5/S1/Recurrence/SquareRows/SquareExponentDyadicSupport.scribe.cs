using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.SquareRows;

internal sealed class SquareExponentDyadicSupportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/SquareRows/SquareExponentDyadicSupport.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/hanna2026a397902");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The zero-constant integer series of OEIS A397902 exists uniquely and has the conjectured odd support at every index above two.",
        H("Square Exponents and the Parity of OEIS A397902"),
        Blocks(
            Paragraph(Text("The source defines A in the ring of integer formal power series, "
                + "with constant coefficient zero, by [X^(m-1)](1-A)^(m squared)/(1-m squared X)=0 "
                + "for every natural m>1. Here invOfUnit means the unique multiplicative inverse "
                + "of the denominator with constant coefficient one; it does not require passage "
                + "to rational coefficients. The sequence term a(n) is [X^n]A.")),
            Node("generatingSeries", "Construction over the integers",
                "Put F=1-A. For n>0 set e=(n+1) squared and g=(1-eX) inverse. Let R be "
                + "[X^n](F^e g), and T be [X^(n-1)](F^(e-1) F' g + F^e g squared). "
                + "Differentiation gives nR=eT. Since e-n(n+2)=1, the residual N=R-(n+2)T "
                + "satisfies R=eN. Changing only the nth coefficient of F changes N by exactly "
                + "that coefficient difference. Iterating the correction F_n -> F_n-N stabilizes "
                + "each coefficient and defines F over the integers, with constant coefficient one. "
                + "The displayed generatingSeries is A=1-F.", DescribeRole.Definition),
            Node("DefiningEquation", "The exact source equation",
                "The predicate includes the zero constant term, integer coefficients, the square "
                + "exponent, and every m>1. Multiplication by invOfUnit expresses precisely the "
                + "division in the OEIS NAME.", DescribeRole.Definition),
            Node("generating_equation", "The constructed series satisfies every row",
                "Coefficient stabilization makes every positive normalized residual zero. "
                + "The identity R=eN then makes every original row zero. The geometric series "
                + "used in the construction equals the denominator's unit inverse."),
            Node("integer_exists_unique", "Integer existence and uniqueness",
                "The preceding construction supplies an integer witness. For uniqueness, equality "
                + "of lower coefficients and the unit multiplier of the normalized residual force "
                + "the next coefficients to agree. Induction proves equality in all degrees. "
                + "No integrality assumption about a rational recurrence is used."),
            Node("a", "Coefficient indexing",
                "This is the source's coefficient indexing, extended by a(0)=0.", DescribeRole.Definition),
            Node("hanna_conjecture", "The complete odd-support classification",
                "Reduce the exact normalized residual to ZMod 2. For the Catalan unit U, "
                + "U=1+X U squared. Set H=U squared, O=(1+X)H, E=1+X+XO, and B=E squared+X O squared. "
                + "Then E+XO=1+X and EO=B. These identities make the odd and even normalized "
                + "rows of B vanish; repeated halving proves the needed diagonal power coefficients "
                + "vanish. Normalized uniqueness identifies B with the reduction of F. "
                + "For n>2, its nth coefficient equals the coefficient of U at floor((n-1)/4). "
                + "The existing binary_catalan theorem identifies this coefficient as one exactly "
                + "when floor((n-1)/4)+1 is a power of two. This gives precisely the four "
                + "indices 2^k, 2^k-1, 2^k-2, 2^k-3 with k>1. Integer uniqueness transfers "
                + "the conclusion to every series satisfying the original defining equation."))));

    private static DocumentBlock Node(string name, string title, string prose,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create("a397902-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromLean(),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);
}
