using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.QuadraticIdeals;

internal sealed class CubicJacobiNormalizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Factorization/QuadraticIdeals/CubicJacobiNormalization.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Euler cubic residue character determines the sign and the chosen ideal of its Eisenstein-valued Jacobi sum.",
        H("Cubic Jacobi Sums and Primary Generators"),
        Blocks(
            Paragraph(Text(
                "Write E = Z[omega], where omega is the standard primitive cube root of unity in the Eisenstein order. "
                + "Let P be a maximal ideal with finite residue field, put q = card(E/P), assume q is congruent to 1 modulo 3, "
                + "and assume 3 is not in P. The character chi_P is the genuine multiplicative character extended by zero at zero, "
                + "whose value at a nonzero residue class is the unique element of {1, omega, omega^2} reducing to x^((q-1)/3). "
                + "Throughout, J_P denotes the Eisenstein-valued Jacobi sum J(chi_P,chi_P).")),
            Describe.Lean(
                DescribeId.Create("cubic-jacobi-character-order"),
                DeclarationHandle.Create(Prefix + "cubicResidueMulChar_orderOf"),
                H("The Euler character has exact order three"),
                StatementSource.FromAuthor(Disp(F.Seq(Parameters(),
                    Call("orderOf", Call("chi", F.Id("P"))), Eq, D(3)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The existing local Euler selector is multiplicative on nonzero residue classes. Extending it by zero "
                    + "therefore gives a MulChar. Its cube is the trivial zero-extended character. If it were itself trivial, "
                    + "every nonzero residue would satisfy x^((q-1)/3) = 1, contradicting the finite-field exponent criterion. "
                    + "The accompanying reduction theorem also covers zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cubic-jacobi-chosen-prime"),
                DeclarationHandle.Create(Prefix + "cubicJacobiSum_mem"),
                H("Euler reduction selects the same prime ideal"),
                StatementSource.FromAuthor(Disp(F.Seq(Parameters(),
                    Call("mem", Jacobi(), F.Id("P"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Reduce the Jacobi sum modulo P and expand (1-x)^m with m = (q-1)/3. Every resulting power "
                    + "has exponent between m and 2m, strictly between zero and q-1. The finite-field power sums vanish. "
                    + "Thus J_P lies in this specified P; no choice between conjugate prime ideals is assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cubic-jacobi-algebraic-norm"),
                DeclarationHandle.Create(Prefix + "cubicJacobiSum_norm"),
                H("The algebraic norm equals the residue cardinality"),
                StatementSource.FromAuthor(Disp(F.Seq(Parameters(),
                    Call("Norm", Jacobi()), Eq, Cardinal()))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Conjugation in E sends the character to its inverse. Embed E into its fraction field to apply "
                    + "the Jacobi product identity; the character and its square are nontrivial by exact order three. "
                    + "Injectivity transports the identity back to E, and the quadratic-algebra norm is J_P times its conjugate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cubic-jacobi-primary-sign"),
                DeclarationHandle.Create(Prefix + "cubicJacobiSum_primary"),
                H("The negative Jacobi sum is primary"),
                StatementSource.FromAuthor(Disp(F.Seq(Parameters(),
                    Call("divides", D(3), F.Seq(Minus, Jacobi(), Minus, D(1)))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The classical Jacobi congruence gives J_P = -1 + z(omega-1)^2. "
                    + "The identity (omega-1)^2 = -3 omega then proves that -J_P is congruent to 1 modulo 3. "
                    + "This fixes the primary sign rather than inserting a sign convention into the final theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cubic-jacobi-principal-ideal"),
                DeclarationHandle.Create(Prefix + "cubicJacobiSum_span"),
                H("The negative Jacobi sum generates the chosen ideal"),
                StatementSource.FromAuthor(Disp(F.Seq(Parameters(),
                    Call("spanSingleton", F.Seq(Minus, Jacobi())), Eq, F.Id("P")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Membership gives the inclusion (-J_P) contained in P. The established integral cyclotomic bridge "
                    + "supplies the principal-ideal structure needed by the absolute-ideal-norm API. The norm computation "
                    + "gives both additive subgroups the same positive finite index. Strict antitonicity of index rules out "
                    + "a proper inclusion, proving equality of ideals."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cubic-jacobi-primary-generator"),
                DeclarationHandle.Create(Prefix + "cubicJacobiSum_eq_primary_generator"),
                H("The primary generator is exactly the negative Jacobi sum"),
                StatementSource.FromAuthor(Disp(F.Seq(Parameters(),
                    Forall, Sp, F.Id("pi"), Colon, Sp, F.Id("E"), Comma, Sp,
                    Call("spanSingleton", F.Id("pi")), Eq, F.Id("P"), Comma, Sp,
                    Call("divides", D(3), F.Seq(F.Id("pi"), Minus, D(1))),
                    Sp, Implies, Sp, Minus, Jacobi(), Eq, F.Id("pi")))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Equal principal ideals make pi and -J_P associates. Reducing the associatedness equation modulo 3 "
                        + "shows that the intervening unit is congruent to 1. The Eisenstein unit norm and integer coordinate "
                        + "bounds force such a unit to be 1. The theorem assumes only that pi generates P and is primary; "
                        + "neither the Jacobi norm nor the selected ideal direction is an extra hypothesis.")),
                    Paragraph(Text(
                        "These are classical cubic character-sum identities, with no mathematical novelty claim. "
                        + "The repository contribution is the complete formal bridge from the existing local Euler selector "
                        + "to exact Jacobi normalization over any finite residue field satisfying the stated assumptions. "
                        + "This is the J = -pi step used in section 58 of the cubic prime-period theory; by itself it does not "
                        + "prove that section's full cubic reciprocity theorem. The classical convention is also recorded in "
                        + "Dunn and Radziwill, arXiv:2109.07463v3, equations (1.4)-(1.5)."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Quotient() => Call("quotient", F.Id("E"), F.Id("P"));
    private static Formula Cardinal() => Call("card", Quotient());
    private static Formula Jacobi() => Call("J", F.Id("P"));
    private static Formula Parameters() => F.Seq(
        Forall, Sp, F.Id("P"), Colon, Sp, Call("Ideal", F.Id("E")), Comma, Sp,
        Call("maximal", F.Id("P")), Comma, Sp, Call("finite", Quotient()), Comma, Sp,
        Call("mod", Cardinal(), D(3)), Eq, D(1), Comma, Sp,
        Call("notMem", D(3), F.Id("P")), Sp, Implies, Sp);
}
