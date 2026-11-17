using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.Heisenberg;

internal sealed class PrimeSquareCoordinatesDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/FiniteGroups/Heisenberg/PrimeSquareCoordinates.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime-square residues and dual numbers have compatible complete residue-coordinate interfaces.",
        H("Prime-square residues and dual numbers"), Blocks(
            Describe.Lean(DescribeId.Create("prime-square-digits"), DeclarationHandle.Create(Owner + "squareCode"),
                H("Two residue digits"), StatementSource.FromAuthor(Disp(Digits())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural prime p, squareCode is an equivalence from ZMod(p*p) to ZMod p times ZMod p. It sends x to its residue x.val modulo p and the residue of the natural quotient x.val/p. Its inverse sends (a,b) to a.val+p*b.val modulo p*p. The canonical representatives of a and b lie below p, so their combined value lies below p*p. The division algorithm proves both inverse laws. Here val denotes the canonical nonnegative representative, and the slash inside NatDiv denotes natural division."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("prime-square-interface"), DeclarationHandle.Create(Owner + "squareCoordinates"),
                H("The integer-residue coordinates"), StatementSource.FromAuthor(Disp(Coordinates("squareCoordinates", Call("ZMod", Call("mul", F.Id("p"), F.Id("p")))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The residue map is the canonical ring homomorphism from ZMod(p*p) to ZMod p. A ring element is a unit exactly when its representative is not divisible by p, equivalently its residue is nonzero. The kernel embedding j(a) is p*a.val modulo p*p. Multiplication gives j(a)*x=j(a*res(x)): changing the integer product by a multiple of p does not affect its product with p modulo p*p. Thus the complete ResidueCoordinates interface, including the nilpotent multiplication law, is proved for this ring."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("prime-dual-interface"), DeclarationHandle.Create(Owner + "dualCoordinates"),
                H("The dual-number coordinates"), StatementSource.FromAuthor(Disp(Coordinates("dualCoordinates", Call("DualNumber", Call("ZMod", F.Id("p")))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A dual number is a pair (a,b), with product (a,b)(c,d)=(ac,ad+bc). The coordinate equivalence is the identity on this product type, res is its first projection, and j(b)=(0,b). Mathlib's unit criterion says that a dual number is a unit exactly when its first coordinate is a unit in the field. Direct coordinate multiplication proves the nilpotent law. Every natural prime, including two, is admitted."))), DescribeRole.Definition))));
    private static Formula Call(string n, params Formula[] a) => new Formula.FunctionCall(FormulaIdentifier.Create(n), [.. a]);
    private static Formula All(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Par(Formula a) => Seq(Open, a, Close);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Digits()
    {
        var p=F.Id("p"); var x=F.Id("x");
        return All("p", Nat(), Imp(Call("NatPrime",p), All("x",Call("ZMod",Call("mul",p,p)),
            Eq(Call("squareCode",p,x),Call("pair",Call("Residue",p,Call("val",x)),Call("Residue",p,Call("NatDiv",Call("val",x),p)))))));
    }
    private static Formula Coordinates(string n, Formula r) => All("p",Nat(),Imp(Call("NatPrime",F.Id("p")),
        Call("HasType",Call(n,F.Id("p")),Call("ResidueCoordinates",r,Call("ZMod",F.Id("p"))))));
}
