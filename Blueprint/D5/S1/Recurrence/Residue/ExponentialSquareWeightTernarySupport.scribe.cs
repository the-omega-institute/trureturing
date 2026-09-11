using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Residue;

internal sealed class ExponentialSquareWeightTernarySupportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Residue/ExponentialSquareWeightTernarySupport.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/hanna2026a397242b");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two modulo-three support conjectures of OEIS A397242 hold in both directions.",
        H("Exponential Square Weights and Ternary Support"),
        Blocks(
            Paragraph(Text("The two conjectures in hanna2026a397242b concern the coefficients "
                + "of A(x)=exp(x+Sum (n^2-1)a(n)x^n/n^2), with the sum over n>=2. "
                + "All indices and exponents below are natural numbers. The function a "
                + "takes integer values, and mod denotes integer remainder. The two "
                + "powers in the residue-two statement are distinct because i<j.")),
            Paragraph(Text("The symbols a and d refer to the imported declarations "),
                Ref("D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.a"),
                Text(" and "),
                Ref("D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.d"),
                Text(". The integral recurrence and normalization are "),
                Ref("D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.d_recurrence"),
                Text(" and "),
                Ref("D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.a_eq"),
                Text(". Their connection to the exponential equation is established by "),
                Ref("D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.log_derivative_identity"),
                Text(", "),
                Ref("D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.coeff_M_rat"),
                Text(", and "),
                Ref("D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.generating_unique"),
                Text(". These give A(0)=1, X A'=M A, the exact rational coefficients "
                    + "of M=X L', and uniqueness with that coefficient shape.")),
            Node("ternary_support_classification", "The complete coefficient classification",
                ClassificationFormula(),
                "Work over ZMod(3). Split the imported recurrence into the three index "
                + "classes. The series U(x)=Sum d(3m+1)x^m and V(x)=Sum d(3m+2)x^m "
                + "satisfy U=1+xVU and V=U-xV^2, so V=1+x^2V^3. Set T=xV and F=xU. "
                + "Then T=x+T^3, F=T+T^2, and F=x+x^2A modulo three. Frobenius and "
                + "strong induction show that T has coefficient one precisely at powers "
                + "of three. The identity F=x+x^2+F^3-xT^3 gives the three coefficient "
                + "recursions for F. Dividing exponents by three proves the displayed "
                + "classification, including the constant coefficient of A.",
                AssessedProvenance.FromRepo()),
            Node("hanna_conjecture_one", "The residue-one conjecture",
                HannaOneFormula(),
                "The classification gives remainder one exactly in its first branch. "
                + "The other branches give remainders two and zero. This proves both "
                + "directions of the first modulo-three conjecture in hanna2026a397242b.",
                AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a397242-mod-three-powers"),
                    ResolutionKind.Proved)),
            Node("hanna_conjecture_two", "The residue-two conjecture",
                HannaTwoFormula(),
                "Ternary induction also proves that a sum of two distinct powers of "
                + "three is neither a single power nor twice a power of three. The "
                + "second branch of the classification therefore applies exactly to "
                + "these sums. This proves both directions of the second modulo-three "
                + "conjecture in hanna2026a397242b.",
                AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a397242-mod-three-sums"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        AssessedProvenance provenance, OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a397242b-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), DescribeRole.Theorem, claim);

    private static Formula N() => F.Id("n");
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Named(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Less(Formula left, Formula right) => Seq(left, Sp, Lt, Sp, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(Parenthesized(value), exponent);
    private static Formula Conjunction(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));
    private static Formula Disjunction(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Lor, Sp, Parenthesized(right));
    private static Formula Implication(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, Parenthesized(conclusion));
    private static Formula Conditional(Formula test, Formula yes, Formula no) => Parenthesized(Seq(
        Named("if"), Sp, Parenthesized(test), Sp, Named("then"), Sp, yes,
        Sp, Named("else"), Sp, no));
    private static Formula Universal(Formula body) => Disp(Seq(
        Forall, Sp, N(), Colon, Sp, Naturals(), Comma, Sp, body));
    private static Formula ExistsNatural(string name, Formula body) => Seq(
        Exists, Sp, F.Id(name), Colon, Sp, Naturals(), Comma, Sp, Parenthesized(body));
    private static Formula Remainder() => new Formula.Modulo(Call("a", N()), D(3));

    private static Formula OneSupport() => Disjunction(
        ExistsNatural("k", Equal(Add(N(), D(2)), Power(D(3), F.Id("k")))),
        ExistsNatural("k", Equal(Add(N(), D(2)), Mul(D(2), Power(D(3), F.Id("k"))))));

    private static Formula TwoSupport() => ExistsNatural("i", ExistsNatural("j",
        Conjunction(Less(F.Id("i"), F.Id("j")), Equal(Add(N(), D(2)),
            Add(Power(D(3), F.Id("i")), Power(D(3), F.Id("j")))))));

    private static Formula ClassificationFormula() => Universal(Equal(Remainder(),
        Conditional(OneSupport(), D(1), Conditional(TwoSupport(), D(2), D(0)))));

    private static Formula HannaOneFormula() => Universal(Implication(Less(D(0), N()),
        Parenthesized(Seq(Equal(Remainder(), D(1)), Sp, Iff, Sp, Parenthesized(OneSupport())))));

    private static Formula HannaTwoFormula() => Universal(Implication(Less(D(0), N()),
        Parenthesized(Seq(Equal(Remainder(), D(2)), Sp, Iff, Sp, Parenthesized(TwoSupport())))));
}
