// UNCOMPILED research Scribe draft for CubicSameCharacteristic.lean.
// The Lean proof assembly and this C# document are uncompiled. No statement
// identity, generated artifact, report, audit, CI, or acceptance is asserted.
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.QuadraticIdeals;

internal sealed class CubicSameCharacteristicDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Factorization/QuadraticIdeals/CubicSameCharacteristic.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A prime-norm argument closes the same-characteristic case and assembles cubic reciprocity for finite maximal quotients.",
        H("Same-Characteristic Primes and Finite-Maximal Cubic Reciprocity"),
        Blocks(
            Paragraph(Text(
                "Uncompiled research draft. These author descriptions follow CubicSameCharacteristic.lean. "
                + "Neither the Lean assembly nor this Scribe document has been compiled here; no kernel, report, audit, "
                + "emission, or acceptance result is claimed.")),
            Paragraph(Text(
                "Fix E = Z[omega]. For each finite maximal quotient, chi_P is the actual Euler cubic residue character "
                + "on E/P, extended by zero at zero, with values in E. The notation chi_P(a) means evaluation at a mod P. "
                + "A primary generator pi satisfies span{pi} = P and 3 divides pi-1. The primary condition itself "
                + "excludes three from P, and the three actual roots in the quotient determine its cardinality modulo three.")),
            Describe.Lean(
                DescribeId.Create("cubic-same-characteristic-cross-data"),
                DeclarationHandle.Create(Prefix + "same_char_cross_data"),
                H("Distinct same-characteristic primes have prime cardinality and conjugate generators"),
                StatementSource.FromAuthor(Disp(F.Seq(
                    ArithmeticParameters(),
                    Forall, Sp, F.Id("p"), Colon, Sp, F.Id("Nat"), Comma, Sp,
                    Call("prime", F.Id("p")), Comma, Sp,
                    Call("CharP", Quotient("P"), F.Id("p")), Comma, Sp,
                    Call("CharP", Quotient("Q"), F.Id("p")), Comma, Sp,
                    PrimaryGenerator("pi", "P"), Comma, Sp, PrimaryGenerator("rho", "Q"), Comma, Sp,
                    Call("notMem", F.Id("pi"), F.Id("Q")), Sp, Implies, Sp,
                    Call("card", Quotient("P")), Eq, F.Id("p"), Sp, Land, Sp,
                    Call("card", Quotient("Q")), Eq, F.Id("p"), Sp, Land, Sp,
                    Call("spanSingleton", Call("star", F.Id("pi"))), Eq, F.Id("Q"), Sp, Land, Sp,
                    F.Id("rho"), Eq, Call("star", F.Id("pi"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This intermediate endpoint explicitly has a common prime characteristic p and pi not in Q, "
                    + "in addition to finite maximal quotients and primary generators. Characteristic p puts p in P, "
                    + "hence p = pi a. Jacobi normalization supplies Norm(pi) = card(E/P), so taking norms shows "
                    + "card(E/P) divides p^2. The prime-power divisor lemma leaves cardinalities p and p^2, since "
                    + "a field has more than one element. In E/Q the factor pi is nonzero; cancelling it from p = pi a "
                    + "puts a in Q. If card(E/P) were p^2, then Norm(a) = 1, making a a unit in this proper ideal, "
                    + "a contradiction. Reversing P and Q gives both cardinalities p. The identity p = pi star(pi) "
                    + "then puts star(pi) in Q, maximality under star gives span{star(pi)} = Q, and primary uniqueness "
                    + "gives rho = star(pi). Thus the inert p^2 case is excluded in this branch by a consumed norm "
                    + "argument, without a splitting classification or an assumed conjugate-field isomorphism. "
                    + "The resulting data meet the hypotheses of the Wilson symbol pair, giving both cross symbols one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cubic-reciprocity-all-finite-maximal-quotients"),
                DeclarationHandle.Create(Prefix + "cubic_reciprocity_primary_finite_maximal"),
                H("Primary cubic reciprocity for all finite maximal quotients"),
                StatementSource.FromAuthor(Disp(F.Seq(
                    ArithmeticParameters(), PrimaryGenerator("pi", "P"), Comma, Sp,
                    PrimaryGenerator("rho", "Q"), Sp, Implies, Sp,
                    Chi("Q", F.Id("pi")), Eq, Chi("P", F.Id("rho"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The final endpoint assumes only maximal ideals P and Q, finiteness of both quotients, "
                    + "specified generators pi and rho of those ideals, and the two primary congruences. "
                    + "It does not assume that P and Q differ, that either cross input is nonzero, any prime or "
                    + "prime-power cardinality formula, a norm identity, a Jacobi or Gauss value, a cube witness, "
                    + "or a symbol comparison. Different characteristics use CubicGaussPrimePower. In the "
                    + "same-characteristic case, if pi belongs to Q, maximality gives P = Q, and rho belongs "
                    + "to P as well; both actual zero-extended characters are zero. Otherwise the preceding "
                    + "prime-norm bridge gives prime cardinalities and conjugate primary generators, so the "
                    + "Wilson pair makes both values one. The equal-ideal zero branch therefore includes the "
                    + "same-characteristic inert situation. Ramified ideals at three cannot have the stated "
                    + "primary generators, as proved internally. This is a statement about finite maximal "
                    + "quotients and their primary generators; it makes no additional claim for arbitrary "
                    + "composite ideals. The result is classical cubic reciprocity, with no mathematical novelty claim."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Cast(Formula value, Formula target) => Call("cast", value, target);
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
