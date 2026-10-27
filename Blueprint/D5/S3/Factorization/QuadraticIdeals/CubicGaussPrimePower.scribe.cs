// UNCOMPILED research Scribe draft for CubicGaussPrimePower.lean.
// No C# compilation, Lean acceptance, emission, statement identity, or report
// has been produced for this document or its generalized Lean endpoints.
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.QuadraticIdeals;

internal sealed class CubicGaussPrimePowerDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Factorization/QuadraticIdeals/CubicGaussPrimePower.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full prime-power Frobenius gives primary cubic reciprocity for finite maximal quotients of different characteristics.",
        H("Prime-Power Frobenius and Cubic Reciprocity"),
        Blocks(
            Paragraph(Text(
                "Uncompiled research draft. The following author descriptions track CubicGaussPrimePower.lean. "
                + "This document has not been compiled or emitted and asserts no kernel, report, audit, or acceptance result.")),
            Paragraph(Text(
                "For the arithmetic endpoint E = Z[omega]. The notation chi_P(a) means the actual zero-extended Euler "
                + "cubic residue character on E/P evaluated at a mod P, with values in E. A primary generator pi of P "
                + "means exactly span{pi} = P and 3 divides pi-1. Write N(P) = card(E/P). The generic finite-sum "
                + "statements retain the ring or field assumptions displayed separately below.")),
            Describe.Lean(
                DescribeId.Create("cubic-gauss-full-prime-power-frobenius"),
                DeclarationHandle.Create(Prefix + "gaussSum_frob_pow"),
                H("Iterate Frobenius before fixing either character"),
                StatementSource.FromAuthor(Disp(F.Seq(
                    Forall, Sp, F.Id("F"), Comma, Sp, F.Id("K"), Comma, Sp,
                    Call("commRing", F.Id("F")), Comma, Sp, Call("finite", F.Id("F")), Comma, Sp,
                    Call("commRing", F.Id("K")), Comma, Sp,
                    Forall, Sp, F.Id("chi"), Colon, Sp, Call("MulChar", F.Id("F"), F.Id("K")), Comma, Sp,
                    Forall, Sp, F.Id("psi"), Colon, Sp, Call("AddChar", F.Id("F"), F.Id("K")), Comma, Sp,
                    Forall, Sp, F.Id("r"), Comma, Sp, F.Id("b"), Colon, Sp, F.Id("Nat"), Comma, Sp,
                    Call("prime", F.Id("r")), Comma, Sp, Call("CharP", F.Id("K"), F.Id("r")),
                    Sp, Implies, Sp,
                    Call("pow", Gauss(F.Id("chi"), F.Id("psi")), PrimePower()), Eq,
                    Gauss(Call("pow", F.Id("chi"), PrimePower()), Call("pow", F.Id("psi"), PrimePower()))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The source has commutative rings F and K, a Fintype on F, arbitrary multiplicative and additive "
                    + "characters, a rational prime r, characteristic r on K, and b any natural number, including zero. "
                    + "It requires neither cubic order nor primitivity nor a congruence on r. The ring homomorphism "
                    + "iterateFrobenius distributes across the whole finite sum and each product, giving the full exponent "
                    + "r^b on both characters. Only after this identity may the cubic character be fixed when r^b is "
                    + "congruent to 1 modulo 3. In particular, when r is congruent to 2 modulo 3 and b is even, one "
                    + "must retain the intermediate character change; assuming r itself is congruent to 1 is unnecessary."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cubic-gauss-target-cardinality-comparison"),
                DeclarationHandle.Create(Prefix + "cubic_gauss_euler_comparison_card"),
                H("Compare at the whole cardinality of the target residue field"),
                StatementSource.FromAuthor(Disp(F.Seq(
                    Forall, Sp, F.Id("F"), Comma, Sp, F.Id("T"), Comma, Sp, F.Id("K"), Comma, Sp,
                    Call("field", F.Id("F")), Comma, Sp, Call("finite", F.Id("F")), Comma, Sp,
                    Call("field", F.Id("T")), Comma, Sp, Call("finite", F.Id("T")), Comma, Sp,
                    Call("field", F.Id("K")), Comma, Sp,
                    Forall, Sp, F.Id("chi"), Colon, Sp, Call("MulChar", F.Id("F"), F.Id("K")), Comma, Sp,
                    Call("orderOf", F.Id("chi")), Eq, D(3), Comma, Sp,
                    Forall, Sp, F.Id("psi"), Colon, Sp, Call("AddChar", F.Id("F"), F.Id("K")), Comma, Sp,
                    Call("primitive", F.Id("psi")), Comma, Sp,
                    Forall, Sp, F.Id("g"), Colon, Sp, Call("ringHom", F.Id("T"), F.Id("K")), Comma, Sp,
                    Call("neq", Call("ringChar", F.Id("T")), Call("ringChar", F.Id("F"))), Comma, Sp,
                    Call("mod", Call("card", F.Id("T")), D(3)), Eq, D(1), Sp, Implies, Sp,
                    Call("inv", Call("chi", Cast(Call("card", F.Id("T")), F.Id("F")))), Eq,
                    Call("pow", Call("mul", Cast(Call("card", F.Id("F")), F.Id("K")),
                        Call("jacobiSum", F.Id("chi"), F.Id("chi"))),
                        Call("natDiv", F.Seq(Call("card", F.Id("T")), Minus, D(1)), D(3)))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "F and T are finite fields; K is a field and need not be finite. The explicit data are a "
                    + "character chi of exact order three, a primitive additive character psi, a ring homomorphism "
                    + "g : T -> K, different characteristics for T and F, and card(T) congruent to 1 modulo 3. "
                    + "Write card(T) = r^b using its own characteristic r. The homomorphism g determines the same "
                    + "characteristic on K, and the distinct-characteristic hypothesis supplies the required nonzero "
                    + "cardinality casts. The convention G = sum_x chi(x) psi(x) yields "
                    + "G^(r^b) = chi(r^b)^(-1) G and G^3 = card(F) J(chi,chi). Cancelling the derived nonzero G "
                    + "gives the displayed inverse-character comparison. Neither a Gauss value nor its nonvanishing "
                    + "is a hypothesis of this cardinality endpoint."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cubic-reciprocity-finite-different-characteristics"),
                DeclarationHandle.Create(Prefix + "cubic_reciprocity_primary_different_char"),
                H("Primary reciprocity includes inert prime-power quotients"),
                StatementSource.FromAuthor(Disp(F.Seq(
                    ArithmeticParameters(),
                    Call("neq", Call("ringChar", Quotient("Q")), Call("ringChar", Quotient("P"))), Comma, Sp,
                    PrimaryGenerator("pi", "P"), Comma, Sp, PrimaryGenerator("rho", "Q"), Sp, Implies, Sp,
                    Chi("Q", F.Id("pi")), Eq, Chi("P", F.Id("rho"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "P and Q are maximal, both quotients are finite, their characteristics differ, and pi and rho "
                    + "are specified primary generators. These are the full arithmetic premises. Primary congruences "
                    + "exclude three from both ideals; the actual cubic roots in each quotient then give N(P) and "
                    + "N(Q) congruent to 1 modulo 3. The proof constructs the needed primitive additive character "
                    + "in a cyclotomic extension of E/Q. Jacobi normalization derives J_P = -pi and Norm(pi) = N(P), "
                    + "so the comparison scalar is -N(P) pi. Restricted injectivity on the three cubic roots lifts "
                    + "the asymmetric comparison chi_P(N(Q)) = chi_Q(pi) chi_Q(star(pi))^2. Repeating it with P and Q "
                    + "interchanged and using the existing cubic algebra lemma gives the stated reciprocity equality. "
                    + "The endpoint has no prime-cardinality, norm, Jacobi-value, Gauss-value, cross-nonzero, or "
                    + "comparison premise. It allows inert cardinalities r^2, including characteristic two and "
                    + "cardinality four. Equal residue characteristics belong to the subsequent same-characteristic "
                    + "module. This is a classical reciprocity formalization; no mathematical novelty is claimed."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Cast(Formula value, Formula target) => Call("cast", value, target);
    private static Formula Gauss(Formula chi, Formula psi) => Call("gaussSum", chi, psi);
    private static Formula PrimePower() => Call("pow", F.Id("r"), F.Id("b"));
    private static Formula Quotient(string ideal) => Call("quotient", F.Id("E"), F.Id(ideal));
    private static Formula Chi(string ideal, Formula value) =>
        Call("chi", F.Id(ideal), Call("modIdeal", value, F.Id(ideal)));
    private static Formula PrimaryGenerator(string element, string ideal) => F.Seq(
        Forall, Sp, F.Id(element), Colon, Sp, F.Id("E"), Comma, Sp,
        Call("spanSingleton", F.Id(element)), Eq, F.Id(ideal), Comma, Sp,
        Call("divides", Cast(D(3), F.Id("E")), F.Seq(F.Id(element), Minus, D(1))));
    private static Formula ArithmeticParameters() => F.Seq(
        Forall, Sp, F.Id("P"), Comma, Sp, F.Id("Q"), Colon, Sp, Call("Ideal", F.Id("E")), Comma, Sp,
        Call("maximal", F.Id("P")), Comma, Sp, Call("maximal", F.Id("Q")), Comma, Sp,
        Call("finite", Quotient("P")), Comma, Sp, Call("finite", Quotient("Q")), Comma, Sp);
}
