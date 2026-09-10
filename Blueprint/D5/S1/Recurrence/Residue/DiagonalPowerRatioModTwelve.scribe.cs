using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Residue;

internal sealed class DiagonalPowerRatioModTwelveDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/Residue/DiagonalPowerRatioModTwelve.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/hanna2026a397241b");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The coefficients of OEIS A397241 are congruent to 11 modulo 12 above degree two.",
        H("Diagonal Power Ratios Modulo Twelve"),
        Blocks(
            Paragraph(Text("The two conjectures are recorded in hanna2026a397241b. The symbols "
                + "a and A denote the existing coefficient function a and generatingSeries "
                + "in DiagonalPowerRatioAllOdd. That module proves generating_equation and "
                + "generating_unique for the normalized integer series. No new coefficient "
                + "sequence is introduced here. All indices and exponents are natural numbers; "
                + "the values a(n) and their remainders are integers.")),
            Paragraph(Text("The operator mk forms a power series from a coefficient function. "
                + "The operator map applies a ring homomorphism coefficientwise, and "
                + "intCast(ZMod(m)) denotes Int.castRingHom(ZMod(m)). In each series identity, "
                + "both sides are over ZMod(m), X is its formal series variable, and the "
                + "constant function passed to mk takes value one in that ring.")),
            Node("mod_three_identity", "The generating series modulo three", SeriesIdentity(D(3)),
                "Put G=mk(1) and B=(1-2X^3)G. In ZMod(3), B^3 is B expanded at X^3. "
                + "Extraction of coefficients in the three residue classes reduces the "
                + "diagonal equation residual to H(n), the degree-n coefficient of "
                + "(1+X)G B^n. The recurrence is H(3n)=H(n), while H(3n+1) and H(3n+2) "
                + "are zero. Strong induction gives H(n)=0 for positive n. Thus B satisfies "
                + "the reduced equation. The leading-coefficient comparison has multiplier "
                + "n^2-(n-1)(n+1)=1, so it identifies B with the reduction of A."),
            Node("mod_four_identity", "The generating series modulo four", SeriesIdentity(D(4)),
                "For the same G and B in ZMod(4), set E=2(XG+X^6). Then E^2=2E=0 and "
                + "B^2 is B expanded at X^2, multiplied by 1+E. A polynomial numerator "
                + "pair P,Q therefore represents the degree-n coefficient of (P+nQ)G^2 B^n. "
                + "Clearing denominators to G^4 gives five pairs closed under even and odd "
                + "coefficient extraction. Their symbolic transitions and strong induction "
                + "show that the initial residual vanishes for every n greater than one. "
                + "The multiplier-one comparison again identifies B with the reduction of A."),
            Node("hanna_conjecture_mod_twelve", "The common remainder modulo twelve",
                Congruence(D(1, 2), D(1, 1)),
                "In both series identities the coefficients above degree two equal minus "
                + "one. Their integer remainders are therefore two modulo three and three "
                + "modulo four. These two remainder equations force the remainder eleven "
                + "modulo twelve."),
            Node("hanna_conjecture_mod_three", "Hanna's conjecture modulo three",
                Congruence(D(3), D(2)),
                "Reducing the common remainder eleven modulo three gives two, for every "
                + "natural index n greater than two.",
                AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a397241-mod-three"),
                    ResolutionKind.Proved)),
            Node("hanna_conjecture_mod_four", "Hanna's conjecture modulo four",
                Congruence(D(4), D(3)),
                "Reducing the common remainder eleven modulo four gives three, for every "
                + "natural index n greater than two.",
                AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a397241-mod-four"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        AssessedProvenance? provenance = null, OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a397241b-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))),
            DescribeRole.Theorem, claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula N() => F.Id("n");
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Less(Formula left, Formula right) => Seq(left, Sp, Lt, Sp, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula Lambda(string name, Formula body) =>
        Parenthesized(Seq(F.Id(name), Colon, Sp, Naturals(), Sp, Mapsto, Sp, body));
    private static Formula Implication(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, Parenthesized(conclusion));

    private static Formula SeriesIdentity(Formula modulus) => Disp(Equal(
        Call("map", Call("intCast", Call("ZMod", modulus)), F.Id("A")),
        Mul(Parenthesized(Subtract(D(1), Mul(D(2), Power(F.Id("X"), D(3))))),
            Call("mk", Lambda("k", D(1))))));

    private static Formula Congruence(Formula modulus, Formula remainder) => Disp(Seq(
        Bound("n", Naturals()), Implication(Less(D(2), N()),
            Equal(new Formula.Modulo(Call("a", N()), modulus), remainder))));
}
