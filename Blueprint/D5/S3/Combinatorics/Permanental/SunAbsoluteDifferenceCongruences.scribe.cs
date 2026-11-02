using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permanental;

internal sealed class SunAbsoluteDifferenceCongruencesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Permanental/SunAbsoluteDifferenceCongruences.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Fourier/sun2022arithmeticpermanents");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both absolute-difference permanent congruences in Sun Conjecture 4.2(i).",
        H("Sun's absolute-difference permanent congruences"),
        Blocks(
            Node("matrix", "A", MatrixBody(), DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source), Blocks(
                    Paragraph(Text("The matrices in (4.3) and (4.4), p. 25, are “per[|j − k|]” and “per[|j − k + 1|]”, with 1 ⩽ j,k ⩽ p. The integer shift s unifies their entries. Source indices are val(j)+1 and val(k)+1; each value is cast to ℤ before subtraction and absolute value.")))),
            Node("claim", "claim", Equal(F.Id("claim"), Parenthesized(ClaimBody())),
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source), Blocks(
                    Paragraph(Text("Conjecture 4.2(i), p. 25: “(i) For any odd prime p, we have per[|j − k|]₁⩽ⱼ,ₖ⩽ₚ ≡ −½ (mod p) and per[|j − k + 1|]₁⩽ⱼ,ₖ⩽ₚ ≡ ½ (mod p).” The displays are (4.3) and (4.4), respectively.")),
                    Paragraph(Text("Nat.Prime and Odd express exactly an odd prime. Matrix.permanent uses the sum of column-indexed permutation products, equal to the source's row-indexed sum by inversion of the permutation. Since 2 is invertible modulo an odd prime, the two integer divisibilities are precisely (4.3) and (4.4). The same p serves both conjuncts.")))),
            Node("alternating-sum", "alternating_sum", AlternatingSumBody(), DescribeRole.Theorem,
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every nonnegative m and integer shift s, the alternating affine sum through 2m is m+s. This telescoping identity supplies the two parity cases in the permanent evaluation.")))),
            Node("result", "result", ClaimBody(), DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source), Blocks(
                    Paragraph(Text("Alternating row and column signs give circulants without changing their permanents. A prime-order fixed-point count on the permutation-weight fibers leaves only translations in characteristic p. Fermat's identity and a telescoping alternating sum then evaluate both permanents. The prime circulant ingredient is the Brualdi–Newman congruence; the two absolute-difference reductions yield the stated divisibilities."))))), []));

    private static Formula MatrixBody()
    {
        var p = F.Id("p");
        var s = F.Id("s");
        var j = F.Id("j");
        var k = F.Id("k");
        return All("p", Naturals(), All("s", Integers(),
            All("j", Call("Fin", p), All("k", Call("Fin", p),
                Equal(Call("A", p, s, j, k),
                    Abs(Add(Sub(Add(Cast(Call("val", j), Integers()), D(1)),
                        Add(Cast(Call("val", k), Integers()), D(1))), s)))))));
    }

    private static Formula ClaimBody()
    {
        var p = F.Id("p");
        var pz = Cast(p, Integers());
        return All("p", Naturals(), ImpliesTo(Apply(Qualified("Nat", "Prime"), p),
            ImpliesTo(Call("Odd", p), And(
                Parenthesized(Divides(pz, Add(Mul(D(2), Apply(Qualified("Matrix", "permanent"),
                    Call("A", p, D(0)))), D(1)))),
                Parenthesized(Divides(pz, Sub(Mul(D(2), Apply(Qualified("Matrix", "permanent"),
                    Call("A", p, D(1)))), D(1))))))));
    }

    private static Formula AlternatingSumBody()
    {
        var m = F.Id("m");
        var s = F.Id("s");
        var r = F.Id("r");
        var index = Seq(r, Sp, Lt, Sp, Add(Mul(D(2), m), D(1)));
        var summand = Mul(new Formula.Power(NegOne(), r),
            Parenthesized(Add(Cast(r, Integers()), s)));
        return All("m", Naturals(), All("s", Integers(),
            Equal(Seq(Sum, Underscore, Grp(index), Sp, summand),
                Add(Cast(m, Integers()), s))));
    }

    private static DocumentBlock Node(string id, string declaration, Formula formula,
        DescribeRole role, AssessedProvenance provenance, BlockSequence prose,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(declaration), StatementSource.FromAuthor(Disp(formula)), provenance, prose, role,
            resolution);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Apply(Formula f, params Formula[] arguments) => new Formula.Apply(f, [.. arguments]);
    private static Formula Qualified(string owner, string name) => Seq(Operatorname, Grp(F.Id(owner), Dot, F.Id(name)));
    private static Formula Parenthesized(Formula a) => Seq(Open, a, Close);
    private static Formula Cast(Formula a, Formula t) => Parenthesized(Seq(a, Colon, t));
    private static Formula NegOne() => Parenthesized(Seq(Minus, Sp, D(1)));
    private static Formula All(string n, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Abs(Formula a) => Seq(Lvert, Sp, a, Rvert, Sp);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Divides(Formula a, Formula b) => Seq(a, Sp, Mid, Sp, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula ImpliesTo(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
}
