using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class SpechtSchurKostkaDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete homogeneous Kostka Gram matrix", H("The complete homogeneous Kostka Gram matrix"), Blocks(
            Paragraph(Text("Iterating Pieri counts tableaux of prescribed content. Consequently the product of complete homogeneous polynomials expands in Schur polynomials with Kostka coefficients. Reading a sorted monomial coefficient gives the Gram matrix of Kostka numbers. Only the number of positive parts of the recorded partition is bounded by the alphabet size.")),
            Describe.Lean(DescribeId.Create("statement-1"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtSchurKostka.coeff_hsymmPart_partWeight"),
                H("Kostka Gram coefficient"), StatementSource.FromAuthor(Disp(Alphabet(All("n", Nat(), All("nu", Part(Id("n")), All("xi", Part(Id("n")), Imp(Call("heightLeAlphabet", Id("xi"), Id("sigma")), Eq(Call("coeff", Call("hsymmPart", Id("sigma"), Id("R"), Id("nu")), Call("partWeight", Id("sigma"), Id("xi"))), SumOver("mu", Part(Id("n")), Mul(Call("natCastK", Id("R"), Id("mu"), Id("nu")), Call("natCastK", Id("R"), Id("mu"), Id("xi"))))))))), "CommSemiring"))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGroups/tauceti2026spechtpolytabloids")),
                Blocks(Paragraph(Text("The notation and hypotheses are specified above."))), DescribeRole.Theorem))));

    private static Formula Id(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => args.Length == 0 ? Seq(Operatorname, Grp(Id(name))) : new Formula.Apply(Seq(Operatorname, Grp(Id(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Mul(Formula a, Formula b) => Seq(Open, a, Close, Sp, Open, b, Close);
    private static Formula SumOver(string name, Formula type, Formula body) => Seq(new Formula.Subscript(Sum, Seq(Id(name), Colon, Sp, type)), Sp, Open, body, Close);
    private static Formula Nat() => Call("Nat");
    private static Formula Part(Formula n) => Call("Partition", n);
    private static Formula Alphabet(Formula body, string ring) => All("sigma", Call("FiniteType"), All("R", Call(ring + "Type"), body));
}
