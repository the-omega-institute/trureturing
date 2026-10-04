using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class AverageMixingDiscriminantIntegralityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Dynamics/AverageMixingDiscriminantIntegrality.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/godsil2013averagemixing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every finite simple graph, the discriminant of the rational minimal polynomial of its adjacency matrix times its average mixing matrix has integer entries.",
        H("The discriminant clears average mixing denominators"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("discriminant-claim"), DeclarationHandle.Create(Prefix + "claim"),
                H("Godsil's Question 1"), StatementSource.FromAuthor(ClaimFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(
                    Text("C. Godsil, Average Mixing of Continuous Quantum Walks, arXiv:1103.2578v3, section 11, Question 1 (page 20), asks: \"Is it true that if D is the discriminant of the minimal polynomial of X, then "),
                    Math(Seq(F.Id("D"), Sp, new Formula.Subscript(Seq(Widehat, Grp(F.Id("M"))), F.Id("X")))),
                    Text(" is an integer matrix?\" Here X is encoded by a simple graph G on Fin n with decidable adjacency; minpoly is taken over the rationals and discr is Polynomial.discr. The real coercions of the rational discriminant and the integer z are displayed explicitly. The average mixing matrix is the source's Lemma 1.1 form (page 3), the sum of the Schur squares of the orthogonal spectral projections over the distinct eigenvalues, as in AverageMixingTraceMaximum.avgMixing. There is no connectedness or simple-spectrum hypothesis. Mathlib assigns discriminant 1 to degree-one and constant polynomials; when n = 0 there are no entry indices."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("discriminant-result"), DeclarationHandle.Create(Prefix + "result"),
                H("An affirmative answer"), StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Write the squarefree minimal polynomial as the product of the factors t minus theta over the distinct eigenvalues. For each theta let q_theta be the product with that factor deleted. Polynomial evaluation at the adjacency matrix gives q_theta(A) = q_theta(theta) E_theta. The resultant identity disc((t - theta) q_theta) = disc(q_theta) q_theta(theta)^2 cancels the squared spectral denominator. Thus each entry of D times the average mixing matrix is the sum over theta of disc(q_theta) times the square of the corresponding entry of q_theta(A). This sum is an integer polynomial in the distinct eigenvalues and is invariant under their permutations. The fundamental theorem of symmetric polynomials expresses it as an integer polynomial in the elementary symmetric functions; Vieta identifies these with signed coefficients of the monic integer minimal polynomial. Consequently every scaled entry is an integer. The argument sharpens the D squared bound in Lemma 3.1 to D."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("godsil-2011-average-mixing-discriminant-integrality"),
                    ResolutionKind.Proved))),
        []));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Some(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Field(string name) => Seq(Mathbb, Grp(F.Id(name)));

    private static Formula ClaimBody()
    {
        Formula n = F.Id("n"), g = F.Id("G"), i = F.Id("i"), j = F.Id("j"), z = F.Id("z");
        Formula vertices = Call("Fin", n);
        Formula discriminant = Call("discr", Call("minpoly", Field("Q"),
            Call("adjMatrix", Field("Q"), g)));
        Formula entry = Call("avgMixing", g, i, j);
        Formula conclusion = Equal(Multiply(Call("algebraMap", Field("Q"), Field("R"), discriminant), entry), Call("algebraMap", Field("Z"), Field("R"), z));
        Formula instances = Seq(OpenBracket, Call("DecidableRel", Call("Adj", g)), CloseBracket,
            Comma, Sp, All("i", vertices, All("j", vertices, Some("z", Field("Z"), conclusion))));
        return All("n", Field("N"), All("G", Call("SimpleGraph", vertices), instances));
    }

    private static Formula ClaimFormula() => Disp(new Formula.Logic(
        F.Id("claim"), FormulaLogicOperator.Iff, Parenthesized(ClaimBody())));
}
