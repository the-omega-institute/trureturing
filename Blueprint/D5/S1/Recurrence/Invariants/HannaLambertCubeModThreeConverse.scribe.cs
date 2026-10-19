using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class HannaLambertCubeModThreeConverseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/HannaLambertCubeModThreeConverse.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2025a382319");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The A382319 coefficient at n and the A382318 coefficient at 3n have the same residue modulo three.",
        H("Hanna's A382319 Congruence Modulo Three"),
        Blocks(
            Paragraph(Text("PowerSeries.coeff extracts rational coefficients. Integer values "
                + "are cast to the rationals in coefficient equalities. Int.ModEq(3,u,v) "
                + "expresses equality of integer residues modulo three. The predicates "
                + "IsA382318 and IsA382319 are those of HannaLambertCubeModThree.")),
            Node("claim", "The coefficient congruence", Disp(Equal(Named("claim"), Parenthesized(ClaimBody()))),
                "OEIS A382319, Comments (unpaginated): \"Conjecture: a(n) == A382318(3*n) "
                + "(mod 3) for n >= 0.\" Here A is the A382318 series and B is the A382319 "
                + "series. Both solutions exist, and every such pair satisfies the displayed "
                + "integer congruence for every natural n, including zero.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The congruence holds", Disp(ClaimBody()),
                "Apply the first coefficient congruence of HannaLambertCubeModThree.result "
                + "and symmetry of Int.ModEq. The existence assertion is the same one.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("hanna319-" + name), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Owner(string name, Formula value) => App(Qualified("HannaLambertCubeModThree", name), value);
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Rationals() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Series() => Call("PowerSeries", Rationals());
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula And(Formula left, Formula right) => Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));
    private static Formula ImpliesTo(Formula premise, Formula conclusion) => Seq(Parenthesized(premise), Sp, Implies, Sp, Parenthesized(conclusion));
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) => Seq(Exists, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Coeff(Formula index, Formula series) => Call("coeff", index, series);
    private static Formula RationalCast(Formula value) => Parenthesized(Seq(value, Colon, Sp, Rationals()));
    private static Formula ModEq(Formula left, Formula right) => App(Qualified("Int", "ModEq"), D(3), left, right);

    private static Formula ClaimBody()
    {
        Formula a = F.Id("A");
        Formula b = F.Id("B");
        Formula n = F.Id("n");
        Formula u = F.Id("u");
        Formula v = F.Id("v");
        Formula pair = And(Owner("IsA382318", a), Owner("IsA382319", b));
        Formula exists = Some("A", Series(), Some("B", Series(), pair));
        Formula residues = All("n", Naturals(), Some("u", Integers(), Some("v", Integers(),
            And(Equal(Coeff(n, b), RationalCast(u)),
                And(Equal(Coeff(Mul(D(3), n), a), RationalCast(v)), ModEq(u, v))))));
        Formula universal = All("A", Series(), All("B", Series(),
            ImpliesTo(Owner("IsA382318", a), ImpliesTo(Owner("IsA382319", b), residues))));
        return And(exists, universal);
    }
}
