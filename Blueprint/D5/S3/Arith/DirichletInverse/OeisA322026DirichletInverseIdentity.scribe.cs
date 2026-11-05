using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.DirichletInverse;

internal sealed class OeisA322026DirichletInverseIdentityDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/DirichletInverse/OeisA322026DirichletInverseIdentity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/oeis2024a322026");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sequence Machine's OEIS A322026 identity with the Dirichlet inverse correction.",
        H("The OEIS A322026 Dirichlet-inverse identity"),
        Blocks(
            Node("a", "The A322026 rank formula", AFormula(),
                "The formal function sets a(0)=0. For positive n, the source formula is A071521(A065331(n)): count nonnegative exponent pairs whose 2,3-number is at most the product of the 2- and 3-adic valuation powers.",
                DescribeRole.Definition),
            Node("b", "The A322026 Dirichlet inverse", BFormula(),
                "b is the integer-valued Dirichlet inverse of a under positive-index Dirichlet convolution; the zero index is carried by the arithmetic-function convention.",
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a322026-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The whole A322026 identity"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The proof uses a(5n)=a(n). A general convolution argument shows that the inverse of any unit-headed arithmetic function with this 5-insensitivity vanishes at every 25n. Therefore a(25n)=a(n) and the inverse correction b(25n) is zero."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a322026-sequence-machine-dirichlet-inverse-identity"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role) => Describe.Lean(
        DescribeId.Create("a322026-" + name),
        DeclarationHandle.Create(Prefix + name),
        H(title),
        StatementSource.FromAuthor(formula),
        AssessedProvenance.FromLiterature(Source),
        Blocks(Paragraph(Text(prose))), role);

    private static Formula AFormula() => Disp(new Formula.Aligned([
        Equal(Call("a", D(0)), D(0)),
        Universal("n", new Formula.Logic(
            new Formula.Relation(D(0), FormulaRelationOperator.LessThan, F.Id("n")),
            FormulaLogicOperator.Implies,
            Equal(Call("a", F.Id("n")),
                Call("latticeCount", Multiply(
                    new Formula.Power(D(2), Call("factorization", F.Id("n"), D(2))),
                    new Formula.Power(D(3), Call("factorization", F.Id("n"), D(3))))))))
    ]));

    private static Formula BFormula() => Disp(Equal(
        F.Id("b"), Call("dirichletInverse", F.Id("a"))));

    private static Formula ResultFormula() => Disp(Universal("n",
        Equal(Call("a", F.Id("n")),
            Add(Call("a", Multiply(D(2, 5), F.Id("n"))),
                Call("b", Multiply(D(2, 5), F.Id("n")))))));

    private static Formula Universal(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name),
            Naturals(), body);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
}
