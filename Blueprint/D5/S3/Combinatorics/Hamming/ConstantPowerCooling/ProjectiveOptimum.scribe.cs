using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Hamming.ConstantPowerCooling;

internal sealed class ProjectiveOptimumDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/Hamming/ConstantPowerCooling/ProjectiveOptimum";
    private const string Paper = "D5/L/Hamming/liuzhangyuzhangji2026optimalcpecc";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An exact cooling-code optimum for a family of finite projective planes with one extra coordinate.",
        H("The exact cooling-code optimum in the projective-plane progression"),
        Blocks(Describe.Lean(DescribeId.Create("support-optimum"),
            DeclarationHandle.Create(Owner + ".support_optimum"),
            H("Exactly n minus one information classes"),
            StatementSource.FromAuthor(OptimumStatement()),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Paper)),
            Blocks(
                Paragraph(Text("For the binary support model the deletion size is two, the word weight is q − 1, "
                    + "and the correction radius is q − 3. At weight q − 1, at most one shared point is "
                    + "equivalent to distance at least 2(q − 3) + 1 because the Hamming distance is even. "
                    + "Every line over the field F has q + 1 points and contributes all of its weight-(q − 1) "
                    + "subsets as one information class. Two deletions leave at least q − 1 points on each line. "
                    + "Distinct lines meet in at most one point. The q(q + 1) + 1 points embed into the coordinate "
                    + "set with one unused coordinate, giving n − 1 classes.")),
                Paragraph(Text("The finite leave bound gives at most n classes. The residue-two equality criterion "
                    + "would give a design with m two-point groups if n were attained. With k = q + 1, the design "
                    + "has n blocks and each point lies in k blocks. Its square integer incidence matrix A has "
                    + "Gram matrix kI + J − P, where J is all ones and P indicates pairs of indices in the same "
                    + "group, including on the diagonal. The m two-by-two blocks in kI − P each have determinant "
                    + "k(k − 2). Adding J multiplies the determinant by 1 + n/(k − 2). Since k − 2 + n = k², the result "
                    + "is k to the power m + 2 times (k − 2) to the power m − 1. The odd exponent on the nonsquare "
                    + "factor gives an odd prime valuation, contradicting the square det(A)².")),
                Paragraph(Text("The field of order seven gives the length-58 result. The theorem also covers "
                    + "nonprime field orders satisfying the disjunction. Section 5's unrestricted even-deletion "
                    + "construction question remains open."))),
            DescribeRole.Theorem)),
        []));

    private static Formula OptimumStatement()
    {
        Formula field = F.Id("F");
        Formula q = F.Id("q");
        Formula n = F.Id("n");
        Formula m = F.Id("m");
        Formula s = F.Id("s");
        Formula p = F.Id("P");
        Formula nat = Seq(Mathbb, Grp(F.Id("N")));
        Formula qPlusOne = Seq(q, Plus, D(1));
        Formula weight = Seq(q, Minus, D(1));
        Formula size = Seq(q, Open, qPlusOne, Close, Plus, D(2));
        Formula oddCase = Seq(Open, Call("Odd", m), Sp, Land, Sp, Neg, Sp,
            Call("IsSquare", qPlusOne), Close);
        Formula evenCase = Seq(Open, Call("Even", m), Sp, Land, Sp, Neg, Sp,
            Call("IsSquare", weight), Close);
        Formula familyType = new Formula.TypeArrow(
            Call("Fin", s), Call("Finset", Call("Finset", Call("Fin", n))));
        Formula family = new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("P"),
            familyType, Call("IsSupportFamily", p, weight, D(2)));
        Formula attained = Seq(OpenBrace, s, Colon, Sp, nat, Sp, Bar, Sp, family, CloseBrace);
        Formula conclusion = Call("IsGreatest", attained, Seq(n, Minus, D(1)));
        return Disp(Seq(Forall, Sp, Open, field, Colon, Sp, F.Id("Type"), Close,
            Sp, OpenBracket, Call("Field", field), CloseBracket,
            Sp, OpenBracket, Call("Finite", field), CloseBracket, Comma, Quad, Sp,
            Operatorname, Grp(F.Id("let")), Sp, q, Eq,
            new Formula.Apply(Seq(F.Id("Nat"), Dot, F.Id("card")), [field]), Comma, Sp,
            n, Eq, size, Comma, Sp, m, Eq, Seq(n, Slash, D(2)), Comma, Quad,
            Open, D(7), Sp, Le, Sp, q, Sp, Land, Sp, Call("Odd", q), Sp, Land, Sp,
            Open, oddCase, Sp, Lor, Sp, evenCase, Close, Close, Sp, Implies, Sp, conclusion));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
