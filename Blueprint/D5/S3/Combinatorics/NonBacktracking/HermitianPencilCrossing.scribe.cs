using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.NonBacktracking;

internal sealed class HermitianPencilCrossingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/NonBacktracking/HermitianPencilCrossing.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/mulaszhangzucal2023nonbacktracking");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A Hermitian affine pencil becomes singular between endpoint subspaces with opposite ordered-eigenvalue signs.",
        H("Hermitian pencil crossing"),
        Blocks(
            Paragraph(Text("For Hermitian matrices A and B, the pencil A minus t times B has ordered eigenvalues that vary continuously with the real parameter t. If a subspace is nonpositive at the left endpoint and another subspace of the complementary dimension is positive at the right endpoint, the indexed eigenvalue crosses zero before the right endpoint.")),
            Describe.Lean(
                DescribeId.Create("pencil-singular-of-subspaces"),
                DeclarationHandle.Create(Prefix + "pencil_singular_of_subspaces"),
                H("A singular point of the pencil"),
                StatementSource.FromAuthor(Disp(CrossingFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The dimension inequality forces the two spectral subspaces to intersect trivially at the left endpoint, while the positive endpoint subspace supplies the opposite sign. Continuity of the selected ordered eigenvalue gives a parameter t in the half-open interval and a nonzero kernel vector."))),
                DescribeRole.Theorem))));

    private static Formula V(string value) => F.Id(value);
    private static Formula Real() => new Formula.NamedConstant(FormulaIdentifier.Create("Real"));
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula QCall(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Qualified(owner, name), [.. args]);
    private static Formula Instance(string name, Formula type) =>
        Seq(OpenBracket, Call(name, type), CloseBracket);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Gt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.GreaterThan, b);
    private static Formula Member(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Neq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Smul(Formula a, Formula b) =>
        Seq(a, Sp, Cdot, Sp, b);
    private static Formula App(Formula f, params Formula[] args) =>
        new Formula.Apply(f, [.. args]);
    private static Formula Complex() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Complex"));
    private static Formula Euclidean(Formula index) =>
        Call("EuclideanSpace", Complex(), index);
    private static Formula MatrixType(Formula index) =>
        Call("Matrix", index, index, Complex());
    private static Formula Hermitian(Formula matrix) =>
        QCall("Matrix", "IsHermitian", matrix);
    private static Formula Rayleigh(Formula matrix, Formula x) =>
        QCall("RCLike", "re", Call("inner", Complex(),
            App(QCall("Matrix", "toEuclideanLin", matrix), x), x));
    private static Formula Pencil(Formula matrix, Formula scalar, Formula other) =>
        Sub(matrix, Smul(QCall("Complex", "ofReal", scalar), other));

    private static Formula CrossingFormula()
    {
        Formula index = V("I");
        Formula matrix = MatrixType(index);
        Formula vector = new Formula.TypeArrow(index, Complex());
        Formula euclideanVector = Euclidean(index);
        Formula a = V("a");
        Formula b = V("b");
        Formula k = V("k");
        Formula w = V("W");
        Formula v = V("V");
        Formula finrankW = QCall("Module", "finrank", Complex(), w);
        Formula finrankV = QCall("Module", "finrank", Complex(), v);
        Formula cardI = QCall("Fintype", "card", index);
        Formula kVal = QCall("Fin", "val", k);
        Formula hW = Gt(Add(Add(finrankW, kVal), D(1)), cardI);
        Formula hV = Eqn(finrankV, Add(kVal, D(1)));
        Formula hneg = All("x", euclideanVector,
            Imp(Member(V("x"), w), Le(Rayleigh(Pencil(V("A"), a, V("B")), V("x")), D(0))));
        Formula hpos = All("x", euclideanVector,
            Imp(Member(V("x"), v),
                Imp(Neq(V("x"), D(0)),
                    Lt(D(0), Rayleigh(Pencil(V("A"), b, V("B")), V("x"))))));
        Formula conclusion = Exists("t", Real(),
            And(Member(V("t"), QCall("Set", "Ico", a, b)),
                Exists("x", vector,
                    And(Neq(V("x"), D(0)),
                        Eqn(QCall("Matrix", "mulVec", Pencil(V("A"), V("t"), V("B")), V("x")), D(0))))));
        Formula body = Imp(Hermitian(V("A")),
            Imp(Hermitian(V("B")),
                All("a", Real(),
                    All("b", Real(),
                        Imp(Le(a, b),
                            All("k", Call("Fin", cardI),
                                All("W", Call("Submodule", Complex(), Euclidean(index)),
                                    All("V", Call("Submodule", Complex(), Euclidean(index)),
                                        Imp(hW, Imp(hV, Imp(hneg, Imp(hpos, conclusion))))))))))));
        body = All("B", matrix, body);
        body = All("A", matrix, body);
        body = All("I", Call("Type"),
            Seq(Instance("Fintype", index), Sp, Instance("DecidableEq", index), Sp, body));
        return body;
    }
}
