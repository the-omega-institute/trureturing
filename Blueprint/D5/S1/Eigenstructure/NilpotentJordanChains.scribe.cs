using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Eigenstructure;

internal sealed class NilpotentJordanChainsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual positive-length Jordan chains and all iterate ranks for a nilpotent operator.",
        H("Nilpotent Jordan Chains"),
        Blocks(Describe.Lean(
            DescribeId.Create("nilpotent-jordan-chains-rank"),
            DeclarationHandle.Create("D5/S1/Eigenstructure/NilpotentJordanChains.nilpotent_jordan_chains_rank"),
            H("A chain basis computes every iterate rank"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("K is any field and V is a finite-dimensional K-vector space. "
                    + "The finite index type I may be empty; each s(i) is a positive natural. "
                    + "Positions(I,s) denotes the dependent sum of Fin(s(i)) over i in I. "
                    + "The basis is ordered along each chain toward its terminal zero. "
                    + "In the conditional formula b(i,j+m) is used only when j+m is below s(i). "
                    + "natSub is truncated natural subtraction.")),
                Paragraph(Text("Mathlib's Module.torsion_by_prime_power_decomposition supplies "
                    + "the complete primary-decomposition induction over K[X]. Nilpotence makes "
                    + "Module.AEval' f torsion by powers of X. AdjoinRoot.powerBasis' gives the "
                    + "basis of each quotient K[X]/(X^s); polynomial linearity transports its shift "
                    + "to f. Removing empty quotient slots leaves positive lengths. The range of "
                    + "each iterate is proved equal to the span of the corresponding basis tails, "
                    + "whose independence computes its dimension. No algebraic closure, invariant "
                    + "complement, or preexisting Jordan basis is assumed."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
    private static Formula Eqn(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula All(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(clauses[i], FormulaLogicOperator.And, result);
        return result;
    }

    private static Formula TheoremFormula()
    {
        Formula k = F.Id("K"), v = F.Id("V"), f = F.Id("f"), index = F.Id("I");
        Formula s = F.Id("s"), b = F.Id("b"), m = F.Id("m"), i = F.Id("i"), j = F.Id("j");
        Formula size = Call("s", i), next = Call("add", j, m);
        Formula action = new Formula.BindMany(FormulaQuantifier.ForAll,
            [Bound("m", Call("Nat")), Bound("i", index), Bound("j", Call("Fin", size))],
            Eqn(Call("apply", Call("pow", f, m), Call("b", i, j)),
                Call("ite", new Formula.Relation(next, FormulaRelationOperator.LessThan, size),
                    Call("b", i, next), D(0))));
        Formula ranks = new Formula.BindMany(FormulaQuantifier.ForAll,
            [Bound("m", Call("Nat"))],
            Eqn(Call("finrank", k, Call("range", Call("pow", f, m))),
                Seq(Sum, Underscore, Grp(i, Sp, InMacro, Sp, index), Sp,
                    Call("natSub", size, m))));
        Formula conclusion = new Formula.BindMany(FormulaQuantifier.Exists,
            [Bound("I", F.Id("Type")), Bound("hI", Call("Fintype", index)),
             Bound("s", Call("Function", index, Call("PNat"))),
             Bound("b", Call("Basis", Call("Positions", index, s), k, v))],
            All(action, ranks));
        return Disp(new Formula.BindMany(FormulaQuantifier.ForAll,
            [Bound("K", F.Id("Type")), Bound("V", F.Id("Type")),
             Bound("f", Call("End", k, v))],
            new Formula.Logic(All(Call("Field", k), Call("AddCommGroup", v),
                Call("Module", k, v), Call("FiniteDimensional", k, v), Call("IsNilpotent", f)),
                FormulaLogicOperator.Implies, conclusion)));
    }
}
