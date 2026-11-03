using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class SpeziaSerpentineHigherExteriorTraceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Matrix/SpeziaSerpentineHigherExteriorTrace.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Eigenstructure/spezia2018a322844");
    private const string Owner = "D5.S3.Quantum.Matrix.SpeziaSerpentineSecondExteriorTrace.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All exterior traces above order two of the serpentine matrix vanish.", H("Spezia’s higher exterior traces"), Blocks(
            Entry("claim", "claim", "Spezia’s second conjecture", new Formula.Logic(V("claim"), FormulaLogicOperator.Iff, Parenthesized(ClaimBody())),
                "A322844 COMMENTS, revision 68, unpaginated: “For k > 2, the trace of the k-th exterior power of the matrix M(n) is equal to zero.” "
                    + "Both n and k range over the naturals. The matrix and the signed characteristic-coefficient exterior trace are those of the second-trace module, including zero for k > n.",
                AssessedProvenance.FromLiterature(Source), DescribeRole.Definition),
            Entry("result", "result", "Every higher exterior trace is zero", ClaimBody(),
                "When k ≤ n, the factor X^(n−2) forces the relevant coefficient to vanish because k > 2. "
                    + "When k > n, the exterior trace is zero by its zero-space case. Thus small matrix orders are included.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula, string prose,
        AssessedProvenance provenance, DescribeRole role) => Describe.Lean(DescribeId.Create(id),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
        Blocks(Paragraph(Text(prose))), role,
        name == "result" ? new OpenProblemResolutionClaim(
            ProblemSlugRef.Create("sp322844-serpentine-higher"), ResolutionKind.Proved) : null);
    private static Formula ClaimBody() => All("n", Nat(), All("k", Nat(), new Formula.Logic(
        Parenthesized(new Formula.Relation(D(2), FormulaRelationOperator.LessThan, V("k"))), FormulaLogicOperator.Implies,
        Parenthesized(new Formula.Relation(Call(Owner + "traceExt", V("k"), Call(Owner + "M", V("n"))), FormulaRelationOperator.Equal, D(0))))));
    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(
        Seq(Operatorname, Grp(Seq(name.Split('.').Select((part, index) =>
            index == 0 ? V(part) : Seq(Dot, V(part))).ToArray()))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp,
        Parenthesized(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
}
