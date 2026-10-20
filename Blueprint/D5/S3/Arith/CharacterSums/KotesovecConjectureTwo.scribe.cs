using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums;

internal sealed class KotesovecConjectureTwoDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/CharacterSums/KotesovecConjectureTwo.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Fourier/kotesovec2024a368959");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every biquadratefree powerful number, and each of 243, 972, 1944 and 2401, has nonzero complete monomial sums at every degree at least two.",
        H("Kotěšovec's second monomial-sum conjecture"),
        Blocks(
            Describe.Lean(DescribeId.Create("kotesovec-two-claim"), DeclarationHandle.Create(Prefix + "claimTwo"),
                H("The second conjecture"), StatementSource.FromAuthor(Disp(Equal(V("claimTwo"), Parenthesized(ClaimBody())))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("OEIS A368959, COMMENTS: \"Conjecture 2: This sequence contains all the terms from A338325, plus 243, 972, 1944, 2401, ...\" The ellipsis is not an exhaustive enumeration: the proposition asserts the inclusion and the four named terms. The predicates InA338325 and InA368959 are those defined in KotesovecConjectureOne."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("kotesovec-two-result"), DeclarationHandle.Create(Prefix + "result"),
                H("The family and four further moduli"), StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Nonvanishing for injective additive characters holds for prime squares, prime cubes, 243 and 2401. Chinese remaindering preserves it for coprime products. The products 972=4*243 and 1944=8*243 yield the remaining two moduli, and the standard additive character gives the exponential sums of A368959."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula ClaimBody() => And(
        Seq(Forall, Sp, V("m"), Colon, Sp, Mathbb, Grp(V("N")), Comma, Sp,
            Parenthesized(Call("InA338325", V("m"))), Sp, Rightarrow, Sp, Parenthesized(Call("InA368959", V("m")))),
        And(Call("InA368959", D(2,4,3)), And(Call("InA368959", D(9,7,2)),
            And(Call("InA368959", D(1,9,4,4)), Call("InA368959", D(2,4,0,1))))));
}
