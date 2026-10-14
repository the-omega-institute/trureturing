using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.AURICOmega;

internal sealed class ExponentialTailDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A geometric estimate for the analytic exponential remainder in a complete normed real algebra.",
        H("Exponential remainder"),
        Blocks(Describe.Lean(DescribeId.Create("auric-omega-exponential-remainder"),
            DeclarationHandle.Create("D5/S3/Quantum/AURICOmega/ExponentialTail.exp_remainder_le"),
            H("A bound from successive factorial ratios"),
            StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Write exponentialRemainder(x,n)=exp(x)-sum from k=0 to n-1 of x^k/k!. Let B be a complete normed real algebra with a submultiplicative norm and norm of the identity equal to one. For a nonnegative r with norm(x) at most r, and r<n+1, the omitted terms of the exponential series have norms bounded by r^n/n! times (r/(n+1))^k. Summing this geometric majorant gives the displayed bound.")),
                Paragraph(Text("Mathlib supplies convergence of the exponential power series, the comparison theorem for sums in normed groups, and the sum of the geometric series. The factorial coefficient estimate joins these results without commuting products. For matrices, the induced maximum row-sum norm is submultiplicative and fits these assumptions; the entrywise maximum norm does not supply that multiplication estimate.")),
                Paragraph(Text("At r=2 and n=13 the ratio is 1/7, so the bound is (7/6) times 2^13/13!. The estimate concerns the actual exponential, rather than only a finite polynomial."))),
            DescribeRole.Theorem))));

    private static Formula Call(string n, params Formula[] x) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(n), [.. x]);
    private static Formula Num(int n) => F.D((byte)n);
    private static Formula Rel(Formula x, FormulaRelationOperator op, Formula y) =>
        new Formula.Relation(x, op, y);
    private static Formula And(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Statement()
    {
        Formula b = F.Id("B"), x = F.Id("x"), r = F.Id("r"), n = F.Id("n");
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula oneMore = new Formula.Binary(n, FormulaBinaryOperator.Add, Num(1));
        Formula assumptions = And(Rel(Num(0), FormulaRelationOperator.LessThanOrEqual, r),
            And(Rel(Call("norm", x), FormulaRelationOperator.LessThanOrEqual, r),
                Rel(r, FormulaRelationOperator.LessThan, oneMore)));
        Formula conclusion = Rel(Call("norm", Call("exponentialRemainder", x, n)),
            FormulaRelationOperator.LessThanOrEqual,
            Call("divide", Call("divide", Call("power", r, n), Call("factorial", n)),
                Call("subtract", Num(1), Call("divide", r, oneMore))));
        Formula body = new Formula.BindMany(FormulaQuantifier.ForAll,
            [new(FormulaIdentifier.Create("x"), b),
             new(FormulaIdentifier.Create("r"), reals),
             new(FormulaIdentifier.Create("n"), naturals)],
            new Formula.Logic(assumptions, FormulaLogicOperator.Implies, conclusion));
        return Disp(new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("B"), Call("Type"),
            Seq(OpenBracket, Call("NormedRing", b), CloseBracket, Sp,
                OpenBracket, Call("NormedAlgebra", reals, b), CloseBracket, Sp,
                OpenBracket, Call("CompleteSpace", b), CloseBracket, Sp,
                OpenBracket, Call("NormOneClass", b), CloseBracket, Sp, body)));
    }
}
