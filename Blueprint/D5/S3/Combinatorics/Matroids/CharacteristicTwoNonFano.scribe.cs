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
                    LibraryNoteRef.Create("D5/L/Combinatorics/blasiak2011lexicographicnetworkcoding")),
                Blocks(Paragraph(Text(
                    "For four arbitrary finite-dimensional submodules over characteristic two, the third opposite intersection "
                    + "is contained in the sum of the first two by the identity (a+b)+(a+c)=b+c. "
                    + "Grassmann's dimension formula bounds each of the first two intersections by the total relation deficiency. "
                    + "The proof allows overlapping, unequal, and zero subspaces. The cited Blasiak–Kleinberg–Lubetzky source supplies "
                    + "the earlier direct-sum projection-cancellation mechanism and codimension robustification; it is attribution, not a proof "
                    + "of this unrestricted declaration. The seven-subspace Phi elimination and the six-party physical bridge remain separate obligations."))),
                DescribeRole.Theorem))));

    private static Formula Statement() =>
        All("F", Type, Inst(A(V("Field"), V("F")),
            Inst(A(V("CharP"), V("F"), D(2)),
                All("V", Type, Inst(A(V("AddCommGroup"), V("V")),
                    Inst(A(V("Module"), V("F"), V("V")),
                        Inst(A(V("FiniteDimensional"), V("F"), V("V")),
                            All("A", Sub(V("F"), V("V")),
                                All("B", Sub(V("F"), V("V")),
                                    All("C", Sub(V("F"), V("V")),
                                        All("Z", Sub(V("F"), V("V")),
                                            Rel(
                                                Call("finrank", V("F"),
                                                    Call("sup",
                                                        Call("sup",
                                                            Call("inf", Call("sup", V("A"), V("B")), Call("sup", V("C"), V("Z"))),
                                                            Call("inf", Call("sup", V("A"), V("C")), Call("sup", V("B"), V("Z")))),
                                                        Call("inf", Call("sup", V("A"), V("Z")), Call("sup", V("B"), V("C"))))),
                                                FormulaRelationOperator.LessThanOrEqual,
                                                Call("mul", D(2), Seq(
                                                    Call("finrank", V("F"), V("A")), Plus,
                                                    Call("finrank", V("F"), V("B")), Plus,
                                                    Call("finrank", V("F"), V("C")), Plus,
                                                    Call("finrank", V("F"), V("Z")), Minus,
                                                    Call("finrank", V("F"),
                                                        Call("sup", Call("sup", Call("sup", V("A"), V("B")), V("C")), V("Z")))))))))))))));))

    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
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
