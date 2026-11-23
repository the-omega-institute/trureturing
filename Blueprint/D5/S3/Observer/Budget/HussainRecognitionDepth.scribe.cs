using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Budget;

internal sealed class HussainRecognitionDepthDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/Budget/HussainRecognitionDepth.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Computability/hussain2026decisiontrees");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact deterministic recognition depth in Hussain's Question 3 stabilizes.",
        H("Eventual constancy of deterministic recognition depth"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("hussain-recognition-depth-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("Question 3"),
                StatementSource.FromAuthor(Disp(Logical(F.Id("claim"), FormulaLogicOperator.Iff, Claim()))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The alphabet A is finite, L is a language over A, and "
                    + "depth(L,n) is the minimum deterministic recognition depth on the length-n "
                    + "promise. The two finite exponent sets define the source's Hom and Het "
                    + "dimensions. An empty exponent set gives dimension zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hussain-recognition-depth-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The exact minimum depth stabilizes"),
                StatementSource.FromAuthor(Disp(Claim())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Below the unique unlabeled root edge, a query node has a nonempty "
                        + "set of distinct letter branches, and each leaf is labeled by a promised "
                        + "word. Each promised input has a compatible complete path, and every "
                        + "compatible path returns that input. The depth bound applies to every "
                        + "complete path. The empty promise has minimum depth zero.")),
                    Paragraph(Text("Complete missing branches by terminating them immediately. "
                        + "Two promised inputs with the same transcript then reach the same leaf. "
                        + "In reverse, label a protocol leaf by the unique promised input reaching "
                        + "it, or by an arbitrary promised word on unreachable leaves. These "
                        + "constructions preserve each depth bound. Querying every coordinate "
                        + "supplies a finite bound, so the two minimum depths exist and agree.")),
                    Paragraph(Text("Given upper bounds m and h for the Hom and Het exponents, "
                        + "put c equal to one plus the alphabet size times the larger bound. "
                        + "For a word of length n+1 with n at least 2c+1, the regions strictly "
                        + "before and after the positions c and c+1 each contain at least c "
                        + "letters. Each region contains at least max(m,h)+1 copies of one letter. "
                        + "The Het bound forces those letters to coincide. The Hom bound forces "
                        + "each intervening letter to be that same letter.")),
                    Paragraph(Text("Delete coordinate c+1. The shorter word belongs to the shorter "
                        + "promise, and inserting the retained letter at coordinate c reconstructs "
                        + "the original word. Relabel the queries of a shorter protocol by the "
                        + "surviving coordinates. This preserves the depth bound and all transcripts "
                        + "on the deletion image, which gives the inequality "),
                        Math(In(Le(Call("depth", F.Id("L"), Add(F.Id("n"), D(1))),
                            Call("depth", F.Id("L"), F.Id("n"))))),
                        Text(" on the tail. A nonincreasing natural-valued sequence is eventually constant."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("hussain-2026-recognition-depth-question-3"),
                    ResolutionKind.Proved)))));

    private static Formula Claim()
    {
        Formula a = F.Id("A"), l = F.Id("L"), n = F.Id("n"), start = F.Id("N"), d = F.Id("d");
        Formula exponentConditions = Logical(Call("Finite", Call("HomExponents", l)),
            FormulaLogicOperator.And, Call("Finite", Call("HetExponents", l)));
        Formula hypotheses = Logical(Le(D(2), Seq(Vert, a, Vert)), FormulaLogicOperator.And,
            Logical(Call("SubwordClosed", l), FormulaLogicOperator.And, exponentConditions));
        Formula settles = Logical(Le(D(1), start), FormulaLogicOperator.And,
            Bind(FormulaQuantifier.ForAll, "n", Naturals(),
                Logical(Le(start, n), FormulaLogicOperator.Implies,
                    Equal(Call("depth", l, n), d))));
        return Bind(FormulaQuantifier.ForAll, "A", Operator("FiniteAlphabet"),
            Bind(FormulaQuantifier.ForAll, "L", Call("Languages", a),
                Logical(Seq(Open, hypotheses, Close), FormulaLogicOperator.Implies,
                    Bind(FormulaQuantifier.Exists, "N", Naturals(),
                        Bind(FormulaQuantifier.Exists, "d", Naturals(), settles)))));
    }

    private static Formula Operator(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Operator(name), [.. args]);
    private static Formula Bind(FormulaQuantifier kind, string name, Formula domain, Formula body) =>
        new Formula.Bind(kind, FormulaIdentifier.Create(name), domain, body);
    private static Formula Logical(Formula left, FormulaLogicOperator op, Formula right) =>
        new Formula.Logic(left, op, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
}
