using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Spectral;

internal sealed class FillmanLimPositiveSemigroupDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Spectral/FillmanLimPositiveSemigroup.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Asymptotics/fillmanlim2026gaprich");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A hyperbolic relative matrix forces a hyperbolic positive product.",
        H("FillmanLimPositiveSemigroup"),
        Blocks(
            Entry("fl-fillmanlimpositivesemigroup-0", "positiveRelativeCriterion", "Hyperbolicity in a positive semigroup",
                All("A", Mat(), All("B", Mat(), Imp(Equal(Det(V("A")), D(1)), Imp(Equal(Det(V("B")), D(1)), Imp(Less(D(2), Abs(Trace(Product(V("A"), App(Q("Matrix", "adjugate"), V("B")))))), Some("C", Mat(), And(Member(V("C"), App(Q("Submonoid", "closure"), new Formula.SetLiteral([V("A"), V("B")]))), Less(D(2), Abs(Trace(V("C"))))))))))), AssessedProvenance.FromRepo(Source),
                "Two determinant-one real matrices with hyperbolic relative product generate a hyperbolic positive product. Elliptic powers approach the adjugate; trace-two generators have affine power traces, which handle both signs at the parabolic boundary.", DescribeRole.Theorem),
            Entry("fl-fillmanlimpositivesemigroup-1", "hyperbolicTracePower", "Positive powers remain hyperbolic",
                All("A", Mat(), Imp(Equal(Det(V("A")), D(1)), Imp(Less(D(2), Abs(Trace(V("A")))), All("n", Nat(), Imp(Less(D(0), V("n")), Less(D(2), Abs(Trace(Power(V("A"), V("n")))))))))), AssessedProvenance.FromRepo(Source),
                "For determinant-one real two by two matrices, absolute trace greater than two persists under every positive integer power. The trace recurrence gives monotone growth after choosing the trace sign.", DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        AssessedProvenance provenance, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role);


    private static Formula V(string name) => F.Id(name);
    private static Formula Q(params string[] parts) => Seq([.. parts.SelectMany((s, i) => i == 0 ? new[] { Operatorname, Grp(F.Id(s)) } : new[] { Dot, Operatorname, Grp(F.Id(s)) })]);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(V(name), args);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, b);
    private static Formula Some(string n, Formula t, Formula b) => Seq(Exists, Sp, V(n), Colon, Sp, t, Comma, Sp, b);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, Parenthesized(b));
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Nat() => V("Nat");
    private static Formula Real() => V("Real");
    private static Formula Mat() => Call("Matrix", Call("Fin", D(2)), Call("Fin", D(2)), Real());
    private static Formula Trace(Formula x) => App(Q("Matrix", "trace"), x);
    private static Formula Det(Formula x) => App(Q("Matrix", "det"), x);
    private static Formula Product(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Star, Sp, Parenthesized(b));
    private static Formula Power(Formula a, Formula b) => new Formula.Power(Parenthesized(a), b);
    private static Formula Abs(Formula x) => Seq(Lvert, Sp, x, Sp, Rvert);
}
