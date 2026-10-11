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
            DescribeId.Create("chain-basis-rank"),
            DeclarationHandle.Create("D5/S1/Eigenstructure/NilpotentJordanChains.chain_basis_rank"),
            H("Every chain basis computes the power ranks"),
            StatementSource.FromAuthor(ChainRankFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For any finite family of positive chain lengths and any basis "
                + "with the displayed shift action, the range of the m-th power is spanned by "
                + "the basis tails starting at position m. Their independence makes its dimension "
                + "the sum of the remaining lengths. The basis index is the dependent sum of "
                + "Fin(val(s(i))); subtraction of natural lengths is truncated."))),
            DescribeRole.Theorem), Describe.Lean(
            DescribeId.Create("nilpotent-jordan-chains-rank"),
            DeclarationHandle.Create("D5/S1/Eigenstructure/NilpotentJordanChains.nilpotent_jordan_chains_rank"),
            H("A chain basis computes every iterate rank"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("K is any field and V is a finite-dimensional K-vector space. "
                    + "The finite index type I may be empty; each s(i) is a positive natural. "
                    + "The basis index is the dependent sum of Fin(val(s(i))) over i in I. "
                    + "The basis is ordered along each chain toward its terminal zero. "
                    + "In the conditional formula b(i,j+m) is used only when j+m is below s(i). "
                    + "Subtraction of natural lengths is truncated.")),
                Paragraph(Text("Mathlib's Module.torsion_by_prime_power_decomposition supplies "
                    + "the complete primary-decomposition induction over K[X]. Nilpotence makes "
                    + "Module.AEval' f torsion by powers of X. AdjoinRoot.powerBasis' gives the "
                    + "basis of each quotient K[X]/(X^s); polynomial linearity transports its shift "
                    + "to f. Removing empty quotient slots leaves positive lengths. The range of "
                    + "each iterate is proved equal to the span of the corresponding basis tails, "
                    + "whose independence computes its dimension. No algebraic closure, invariant "
                    + "complement, or preexisting Jordan basis is assumed."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args)
    {
        var symbol = Seq(Operatorname, Grp(name.Split('.').SelectMany((part, i) =>
            i == 0 ? new[] { F.Id(part) } : new Formula[] { new Formula.LatexSymbol(FormulaLatexSymbol.Period), F.Id(part) }).ToArray()));
        return args.Length == 0 ? symbol : new Formula.Apply(symbol, [.. args]);
    }
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Assumption(Formula x, Formula body) =>
        Seq(OpenBracket, x, CloseBracket, Sp, body);
    private static Formula Bind(FormulaQuantifier quantifier, string name, Formula type, Formula body) =>
        new Formula.Bind(quantifier, FormulaIdentifier.Create(name),
            type is Formula.TypeArrow ? Parenthesized(type) : type, body);
    private static Formula All(string name, Formula type, Formula body) =>
        Bind(FormulaQuantifier.ForAll, name, type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Bind(FormulaQuantifier.Exists, name, type, body);
    private static Formula Eqn(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula At(Formula f, Formula x) => new Formula.Apply(f, [x]);
    private static Formula Pair(Formula x, Formula y) =>
        Seq(Langle, x, Comma, Sp, y, Rangle);
    private static Formula Nats => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Length(Formula i) => Call("val", At(F.Id("s"), i));
    private static Formula Positions => Parenthesized(Seq(Sigma, Sp,
        Parenthesized(Seq(F.Id("i"), Sp, Colon, Sp, F.Id("I"))), Comma, Sp,
        Call("Fin", Length(F.Id("i")))));
    private static Formula BasisType => Call("Basis", Positions, F.Id("K"), F.Id("V"));
    private static Formula LengthType => new Formula.TypeArrow(F.Id("I"), Call("PNat"));
    private static Formula Power => new Formula.Power(Parenthesized(F.Id("f")), F.Id("m"));

    private static Formula Action()
    {
        var i = F.Id("i"); var j = F.Id("j"); var m = F.Id("m");
        var size = Length(i);
        var next = Seq(Call("val", j), Sp, Plus, Sp, m);
        var nextIndex = Parenthesized(Seq(Call("Fin.mk", next), Sp, Colon, Sp, Call("Fin", size)));
        return All("m", Nats, All("i", F.Id("I"), All("j", Call("Fin", size),
            Eqn(At(Power, At(F.Id("b"), Pair(i, j))),
                Call("ite", new Formula.Relation(next, FormulaRelationOperator.LessThan, size),
                    At(F.Id("b"), Pair(i, nextIndex)), D(0))))));
    }

    private static Formula Ranks() => All("m", Nats,
        Eqn(Call("Module.finrank", F.Id("K"), Call("LinearMap.range", Power)),
            Seq(new Formula.Subscript(Sum, Seq(F.Id("i"), Sp, Colon, Sp, F.Id("I"))), Sp,
                Parenthesized(Seq(Length(F.Id("i")), Sp, Minus, Sp, F.Id("m"))))));

    private static Formula Environment(Formula body, bool finiteDimensional) =>
        All("K", Call("Type"), All("V", Call("Type"),
            Assumption(Call("Field", F.Id("K")),
                Assumption(Call("AddCommGroup", F.Id("V")),
                    Assumption(Call("Module", F.Id("K"), F.Id("V")), finiteDimensional
                        ? Assumption(Call("FiniteDimensional", F.Id("K"), F.Id("V")), body)
                        : body)))));

    private static Formula TheoremFormula()
    {
        var conclusion = Some("I", Call("Type"), Assumption(Call("Fintype", F.Id("I")),
            Some("s", LengthType, Some("b", BasisType, And(Action(), Ranks())))));
        return Disp(Environment(All("f", Call("Module.End", F.Id("K"), F.Id("V")),
            Implies(Call("IsNilpotent", F.Id("f")), conclusion)), true));
    }

    private static Formula ChainRankFormula() => Disp(Environment(
        All("I", Call("Type"), Assumption(Call("Fintype", F.Id("I")),
            All("f", Call("Module.End", F.Id("K"), F.Id("V")),
                All("s", LengthType, All("b", BasisType, Implies(Action(), Ranks())))))), false));
}
