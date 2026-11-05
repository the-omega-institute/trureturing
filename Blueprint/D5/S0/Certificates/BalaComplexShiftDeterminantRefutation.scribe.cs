using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class BalaComplexShiftDeterminantRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/BalaComplexShiftDeterminantRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/bala2023a086205");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A one-by-one determinant refutes the arbitrary complex shift in OEIS A086205.",
        H("Bala's Complex-Shift Determinant Conjecture"),
        Blocks(
            Describe.Lean(DescribeId.Create("a086205-shifted-determinant"),
                DeclarationHandle.Create(Prefix + "shiftedDet"),
                H("The generalized-binomial determinant"),
                StatementSource.FromAuthor(DetFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Rows and columns run from one through n. For complex w and natural k, "
                    + "choose(w,k) is the falling factorial w(w-1)...(w-k+1) divided by k!, "
                    + "as given by Ring.choose and Ring.choose_eq_smul. The product for k = 0 "
                    + "is one. At n = 0 the matrix is empty and its determinant is one."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a086205-shift-conjecture"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The arbitrary-complex-shift assertion"),
                StatementSource.FromAuthor(Disp(new Formula.Logic(F.Id("claim"),
                    FormulaLogicOperator.Iff, ClaimBody()))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The unshifted determinant defines A086205(n). The conjecture asserts "
                    + "equality for every natural n, including zero, and every complex shift z."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a086205-shift-refuted"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The assertion is false"),
                StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For n = 1 and z = 1 the only entry is choose(2,1) = 2, whereas "
                    + "the unshifted entry is choose(1,1) = 1. A one-by-one determinant "
                    + "equals its entry. The asserted equality would imply 2 = 1 in "
                    + "the complex numbers, refuting the printed universal assertion."))),
                DescribeRole.Theorem))));

    private static Formula ClaimBody()
    {
        var n = F.Id("n"); var z = F.Id("z");
        return All("n", Naturals(), All("z", Complexes(),
            Equal(Call("shiftedDet", n, z), Call("shiftedDet", n, D(0)))));
    }

    private static Formula DetFormula()
    {
        var n = F.Id("n"); var z = F.Id("z");
        var i = F.Id("i"); var j = F.Id("j");
        var entries = new Formula.Subscript(
            Seq(OpenBracket, Call("choose", Add(Power(Add(i, D(1)), D(2)), z),
                Add(j, D(1))), CloseBracket),
            Seq(i, Comma, Sp, j, Sp, InMacro, Sp, Call("Fin", n)));
        return Disp(All("n", Naturals(), All("z", Complexes(),
            Equal(Call("shiftedDet", n, z), Call("det", entries)))));
    }

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Equal(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Power(Formula a, Formula b) => new Formula.Power(a, b);
}
