using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Wythoff;

internal sealed class ColumnResiduePairsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/kimberling2025a035513");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The first two Wythoff columns attain all residue pairs modulo every positive integer.",
        H("Wythoff column residue pairs"),
        Blocks(
            Paragraph(Text("Write phi=(1+sqrt(5))/2. Rows and columns start at one. "
                + "The array W has W(n,0)=floor(n phi), "
                + "W(n,1)=floor(floor(n phi) phi), "
                + "W(n,2)=floor(floor(n phi) phi^2), and "
                + "W(n,k+2)=W(n,k+1)+W(n,k) for k>=1. "
                + "Its first row is 1,2,3,5,... . Let R(m) be the image of positive "
                + "row indices under n -> (W(n,1) mod m,W(n,2) mod m). "
                + "Let w(m,n,k) denote W(n,k) reduced to ZMod(m).")),
            Describe.Lean(
                DescribeId.Create("wythoff-column-residue-pairs-result"),
                DeclarationHandle.Create("D5/S3/Arith/Wythoff/ColumnResiduePairs.result"),
                H("All-modulus residue coverage"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The two floor expressions simplify to "
                    + "floor(n phi)+n-1 and 2 floor(n phi)+n-1. Given residues a,b, "
                    + "choose r=2a-b and s=b-a. Along positive indices n=r+1+mk, "
                    + "irrational rotation on the circle of circumference m is dense. "
                    + "An open interval between s and s+1 therefore supplies "
                    + "floor(n phi)=s modulo m, and the linear formulas give a,b. "
                    + "The image is the full product, which has m^2 elements. "
                    + "The modulus-one case strengthens Kimberling's m>=2 assertion."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a035513-wythoff-column-residue-pairs"),
                    ResolutionKind.Proved)))));

    private static Formula ResultFormula()
    {
        Formula m = F.Id("m"), n = F.Id("n"), a = F.Id("a"), b = F.Id("b");
        Formula nat = Seq(Mathbb, Grp(F.Id("N")));
        Formula residues = Call("ZMod", m);
        Formula witness = new Formula.Bind(FormulaQuantifier.Exists,
            FormulaIdentifier.Create("n"), nat,
            And(Le(D(1), n), And(Eq(Call("w", m, n, D(1)), a),
                Eq(Call("w", m, n, D(2)), b))));
        Formula coverage = new Formula.BindMany(FormulaQuantifier.ForAll,
            [new(FormulaIdentifier.Create("a"), residues),
             new(FormulaIdentifier.Create("b"), residues)], witness);
        return Disp(new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("m"), nat,
            new Formula.Logic(Le(D(1), m), FormulaLogicOperator.Implies,
                And(Eq(Call("ncard", Call("R", m)), new Formula.Power(m, D(2))), coverage))));
    }

    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(F.Id(name), [.. args]);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
}
