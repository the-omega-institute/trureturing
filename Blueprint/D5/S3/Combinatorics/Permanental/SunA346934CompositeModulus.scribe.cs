using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permanental;

internal sealed class SunA346934CompositeModulusDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Permanental/SunA346934CompositeModulus.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/sun2021a346934");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every positive n with composite 2*n+1, that modulus divides the signed-difference permanent.",
        H("Sun A346934: the composite-modulus sentence"),
        Blocks(
            Node("sequence", "a", All("n", Naturals(),
                Equal(Call("a", F.Id("n")), PermanentBody())),
                "OEIS A346934 revision 29, NAME (unpaginated): \"Permanent of the 2n X 2n matrix with the (i,j)-entry i-j (i,j=1..2n).\" The type Fin (2*n) represents these indices through val i + 1. Each entry and the permanent are integers. Matrix.permanent sums products of M (sigma i) i; inversion of permutations gives the source's row-first sum.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "claim", Iff(F.Id("claim"), ClaimBody()),
                "OEIS A346934 revision 29, COMMENT, Conjecture 1 (unpaginated): \"Conjecture 1: (-1)^n*a(n) > 0 for all n > 0. Also, a(n) == 0 (mod 2n+1) if 2n+1 is composite.\" The formula expresses the sentence beginning Also. Natural n starts at 1, as specified by the sequence offset 1,2. Since 2*n+1 is at least 3, its nonprimality is exactly compositeness; divisibility in the integers expresses the zero congruence. The sign sentence and Conjecture 2 are outside this proposition.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "result", ClaimBody(),
                "Expanding the additive integer matrix permanent and grouping permutations by their subset images gives factorial-split multiplicities. At order q-1, every multiplicity is divisible by the odd composite modulus q. Distinct factors in the larger factorial prove this divisibility, with the three central products 720, 576 and 720 treating q = 9. Taking q = 2*n+1 proves the stated divisibility for the signed-difference matrix.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))), []));

    private static DocumentBlock Node(string id, string declaration, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(declaration), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula ClaimBody() => All("n", Naturals(),
        ImpliesTo(LeqTo(D(1), F.Id("n")),
            ImpliesTo(Not(Apply(Qualified("Nat", "Prime"), Modulus())),
                Divides(Cast(Cast(Modulus(), Naturals()), Integers()), Call("a", F.Id("n"))))));

    private static Formula PermanentBody() => Apply(Qualified("Matrix", "permanent"),
        Parenthesized(LambdaOf("i", Call("Fin", Multiply(D(2), F.Id("n"))),
            LambdaOf("j", Call("Fin", Multiply(D(2), F.Id("n"))),
                Subtract(Parenthesized(Add(Cast(Call("val", F.Id("i")), Integers()), D(1))),
                    Parenthesized(Add(Cast(Call("val", F.Id("j")), Integers()), D(1))))))));

    private static Formula Modulus() => Add(Multiply(D(2), F.Id("n")), D(1));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner), Dot, F.Id(name)));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(F.Id("fun"), Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)),
            Sp, Mapsto, Sp, body);
    private static Formula Cast(Formula value, Formula type) =>
        Parenthesized(Seq(value, Sp, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula LeqTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Divides(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Divides, right);
    private static Formula ImpliesTo(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula Not(Formula value) => Seq(Neg, Sp, Parenthesized(value));
}
