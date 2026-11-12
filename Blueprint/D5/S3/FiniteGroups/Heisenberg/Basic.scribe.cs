using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.Heisenberg;

internal sealed class HeisenbergBasicDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/FiniteGroups/Heisenberg/Basic.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGroups/tauceti2026heisenberg");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Heisenberg triples over a ring have explicit cardinality, powers and derived subgroup.",
        H("Heisenberg triples"), Blocks(
            Describe.Lean(DescribeId.Create("heisenberg-card"), DeclarationHandle.Create(Owner + "card_eq"),
                H("The cardinality of triples"), StatementSource.FromAuthor(Disp(All("R", Call("Type"),
                    Eq(Call("NatCard", Call("HeisenbergGroup", F.Id("R"))), Pow(Call("NatCard", F.Id("R")), D(3)))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("HeisenbergGroup R consists of all triples (x,y,z) of ring elements. The underlying type is equivalent to R times R times R, so its natural cardinality is the cube of the coefficient cardinality. The type-level statement also covers infinite carriers under Nat.card. Multiplication is (x,y,z)(X,Y,Z)=(x+X,y+Y,z+Z+xY), identity is (0,0,0), and the inverse is (−x,−y,−z+xy)."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("heisenberg-powers"), DeclarationHandle.Create(Owner + "pow_eq"),
                H("Powers without division by two"), StatementSource.FromAuthor(Disp(All("R", Call("Type"), Ring(F.Id("R"),
                    All("a", Call("HeisenbergGroup", F.Id("R")), All("n", Nat(), Eq(Pow(F.Id("a"), F.Id("n")),
                        Call("triple", Call("nsmul", F.Id("n"), Call("x", F.Id("a"))),
                            Call("nsmul", F.Id("n"), Call("y", F.Id("a"))),
                            Call("add", Call("nsmul", F.Id("n"), Call("z", F.Id("a"))),
                                Call("nsmul", Call("choose", F.Id("n"), D(2)), Call("mul", Call("x", F.Id("a")), Call("y", F.Id("a"))))))))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every ring, every triple a and every natural n, the first coordinates of a to the n are n times x and n times y. Its third coordinate is n times z plus n choose two times xy. Here nsmul is repeated addition and choose is the natural binomial coefficient. This form requires no inverse of two and applies in characteristic two. Induction uses the group multiplication and Pascal's binomial identity."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("heisenberg-derived-axis"), DeclarationHandle.Create(Owner + "commutator_eq_zAxis"),
                H("The derived subgroup is the central axis"), StatementSource.FromAuthor(Disp(All("R", Call("Type"), Ring(F.Id("R"),
                    Eq(Call("commutator", Call("HeisenbergGroup", F.Id("R"))), Call("zAxis", F.Id("R"))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The native commutator a*b*a inverse*b inverse is (0,0,xY−Xy). Thus every commutator belongs to the z-axis, the subgroup defined by x=y=0. Conversely (0,0,c) is the commutator of (c,0,0) and (0,1,0), so the generated subgroup is the entire axis. The generic group, cardinality, power and axis results are due to The Tau Ceti contributors, in the cited immutable source. Their Apache-2.0 copyright and license are retained with the Lean source. The source-commutator convention is connected separately by inversion of both generators."))), DescribeRole.Theorem))));

    private static Formula Call(string n, params Formula[] a) => new Formula.FunctionCall(FormulaIdentifier.Create(n), [.. a]);
    private static Formula All(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Ring(Formula r, Formula b) => Seq(OpenBracket, Call("Ring", r), CloseBracket, Sp, b);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
}
