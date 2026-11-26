using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates.Combinatorics;

internal sealed class ForcedLastPairPfaffianDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/Combinatorics/ForcedLastPairPfaffian.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A zero penultimate upper column forces a final pair in the normalized Pfaffian over any commutative ring.",
        H("A forced final pair in a normalized Pfaffian"),
        Blocks(
            Describe.Lean(DescribeId.Create("embed"), DeclarationHandle.Create(Prefix + "embed"),
                H("Prefix inclusion"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural n, embed sends i in Fin(2n) to the index of the same value in Fin(2(n+1))."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("last-zero"), DeclarationHandle.Create(Prefix + "last0"),
                H("Penultimate index"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural n, last0(n) is the index of value 2n in Fin(2(n+1))."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("last-one"), DeclarationHandle.Create(Prefix + "last1"),
                H("Last index"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural n, last1(n) is the index of value 2n+1 in Fin(2(n+1))."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("forced-last-pair"), DeclarationHandle.Create(Prefix + "pfaffian_forced_last_pair"),
                H("Forced final pair"), StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let R be any commutative ring and A any matrix on Fin(2(n+1)), for n a natural number. For every earlier index i in Fin(2n), assume A(embed(i),last0(n))=0. Every nonzero normalized listing term must pair last0(n) with last1(n). The surviving listings are precisely the extensions of normalized prefix listings, with the final pair appended. The extension preserves the permutation sign, and the added factor is A(last0(n),last1(n)). Summing gives the equality, including n=0. The Pfaffian here is the repository's normalized pair-listing sum, and no skew-symmetry hypothesis is required."))), DescribeRole.Theorem)
        )));

    private static Formula Statement()
    {
        Formula r = F.Id("R"), n = F.Id("n"), a = F.Id("A"), i = F.Id("i");
        Formula size = Mul(D(2), Add(n, D(1)));
        Formula zero = Call("last0", n), one = Call("last1", n);
        Formula hypothesis = All("i", Fin(Mul(D(2), n)), Eq(Apply(F.Id("A"), Call("embed", i), zero), D(0)));
        Formula conclusion = Eq(Call("pfaffian", a),
            Mul(Call("pfaffian", Call("submatrix", a, F.Id("embed"), F.Id("embed"))), Apply(F.Id("A"), zero, one)));
        return Disp(All("R", F.Id("Type"), Seq(OpenBracket, Call("CommRing", r), CloseBracket, Sp,
            All("n", Nat, All("A", Call("Matrix", Fin(size), Fin(size), r), Imp(hypothesis, conclusion))))));
    }

    private static Formula Apply(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);

    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));


    private static Formula Fin(Formula a) => Call("Fin", a);

}
