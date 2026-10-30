using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class CharacteristicTwoNonFanoDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/CharacteristicTwoNonFano.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Characteristic-two opposite intersections obey an arbitrary-dimensional relation-deficiency bound.",
        H("Characteristic-two opposite intersections"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finrank-opposite-sum-le-two-deficiency"),
                DeclarationHandle.Create(Module + "finrank_opposite_sum_le_two_deficiency"),
                H("Three opposite intersections are controlled by twice the relation deficiency"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Entropy/blasiak2011lexicographicnetworkcoding")),
                Blocks(Paragraph(Text(
                    "For four arbitrary finite-dimensional submodules over characteristic two, the third opposite intersection "
                    + "is contained in the sum of the first two by the identity (a+b)+(a+c)=b+c. "
                    + "Grassmann's dimension formula bounds each of the first two intersections by the total relation deficiency. "
                    + "The proof allows overlapping, unequal, and zero subspaces. The cited Blasiak–Kleinberg–Lubetzky source supplies "
                    + "the earlier direct-sum projection-cancellation mechanism and codimension robustification; it is attribution, not a proof "
                    + "of this unrestricted declaration. The seven-subspace Phi elimination and the six-party physical bridge remain separate obligations."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula Dim(Formula subspace) => Call("finrank", V("F"), subspace);
        Formula Sup(Formula left, Formula right) => Call("sup", left, right);
        Formula Inf(Formula left, Formula right) => Call("inf", left, right);
        var a = V("A");
        var b = V("B");
        var c = V("C");
        var z = V("Z");
        var first = Inf(Sup(a, b), Sup(c, z));
        var second = Inf(Sup(a, c), Sup(b, z));
        var third = Inf(Sup(a, z), Sup(b, c));
        var deficiency = Parenthesized(Seq(
            Dim(a), Plus, Dim(b), Plus, Dim(c), Plus, Dim(z), Minus,
            Dim(Sup(Sup(Sup(a, b), c), z))));
        var bound = Rel(Dim(Sup(Sup(first, second), third)),
            FormulaRelationOperator.LessThanOrEqual, Call("mul", D(2), deficiency));
        var submodule = Sub(V("F"), V("V"));
        var subspaces = All("A", submodule, All("B", submodule,
            All("C", submodule, All("Z", submodule, bound))));
        var space = All("V", Type, Inst(A(V("AddCommGroup"), V("V")),
            Inst(A(V("Module"), V("F"), V("V")),
                Inst(A(V("FiniteDimensional"), V("F"), V("V")), subspaces))));
        return All("F", Type, Inst(A(V("Field"), V("F")),
            Inst(A(V("CharP"), V("F"), D(2)), space)));
    }

    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
    private static Formula A(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Inst(Formula type, Formula body) =>
        Seq(OpenBracket, type, CloseBracket, Sp, body);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Sub(Formula field, Formula space) => A(V("Submodule"), field, space);
    private static Formula Type => V("Type");
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
