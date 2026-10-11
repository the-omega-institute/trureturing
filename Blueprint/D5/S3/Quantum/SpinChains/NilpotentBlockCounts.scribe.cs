using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.SpinChains;

internal sealed class NilpotentBlockCountsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Intrinsic nilpotent block counts are determined by all iterate ranks.",
        H("Intrinsic nilpotent block counts"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nilpotent-block-counts-c"),
                DeclarationHandle.Create("D5/S3/Quantum/SpinChains/NilpotentBlockCounts.C"),
                H("Kernel intersections with preceding power ranges"),
                StatementSource.FromAuthor(Disp(CDefinition())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a field K, a finite-dimensional K-vector space V, an endomorphism N, and a natural index j, C N j is the intersection of ker N with the range of N raised to j minus one. At j equal to one this is ker N. The successor spaces form a descending sequence."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("nilpotent-block-counts-block-count"),
                DeclarationHandle.Create("D5/S3/Quantum/SpinChains/NilpotentBlockCounts.blockCount"),
                H("Successive quotient dimensions"),
                StatementSource.FromAuthor(Disp(BlockCountDefinition())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The block count at j is the K-dimension of C N j modulo the copy of C N (j plus one) inside C N j. This quotient records the new kernel vectors that first occur at that level."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("nilpotent-block-counts-rank-formula"),
                DeclarationHandle.Create("D5/S3/Quantum/SpinChains/NilpotentBlockCounts.blockCount_rank_formula"),
                H("The rank formula for intrinsic block counts"),
                StatementSource.FromAuthor(Disp(RankFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For j at least one, the map N restricted to range N raised to j minus one has image range N raised to j and kernel C N j. Rank-nullity therefore gives the additive identity dim C N j plus rho(j) equals rho(j minus one). Applying this identity at j and at j plus one, together with the quotient dimension identity for C N j modulo C N (j plus one), yields the displayed integer formula. The calculation stays in integer casts of additive equalities and does not use truncated natural subtraction."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nilpotent-block-counts-rank-determines-count"),
                DeclarationHandle.Create("D5/S3/Quantum/SpinChains/NilpotentBlockCounts.blockCount_eq_of_range_finrank_eq"),
                H("Iterate ranks determine every block count"),
                StatementSource.FromAuthor(Disp(DeterminesCount())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If two endomorphisms over the same field have equal finite-dimensional ranks for every natural power, the rank formula gives equal block counts at every index. The index zero quotient is zero on both sides, and positive indices use the formula."))),
                DescribeRole.Theorem)
        )));

    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? Seq(Operatorname, Grp(F.Id(name))) :
            new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Eq(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Le(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Implies(Formula x, Formula y) =>
        new Formula.Logic(Parenthesized(x), FormulaLogicOperator.Implies, Parenthesized(y));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Assumption(Formula x, Formula body) =>
        Seq(OpenBracket, x, CloseBracket, Sp, body);
    private static Formula Sub(Formula x, Formula y) => Seq(x, Sp, Minus, Sp, y);
    private static Formula Add(Formula x, Formula y) => Seq(x, Sp, Plus, Sp, y);
    private static Formula Mul(Formula x, Formula y) => Seq(x, Sp, Times, Sp, y);
    private static Formula Power(Formula x, Formula y) => new Formula.Power(Parenthesized(x), y);
    private static Formula CastInt(Formula x) => Call("IntCast", x);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Type() => Call("Type");
    private static Formula End(Formula k, Formula v) => Call("End", k, v);
    private static Formula CAt(Formula n, Formula j) => Call("C", n, j);
    private static Formula BlockAt(Formula n, Formula j) => Call("blockCount", n, j);
    private static Formula Range(Formula n, Formula r) => Call("range", Power(n, r));
    private static Formula Rho(Formula n, Formula r) => Call("finrank", F.Id("K"), Range(n, r));

    private static Formula CDefinition()
    {
        var k = F.Id("K"); var v = F.Id("V"); var n = F.Id("N"); var j = F.Id("j");
        var rhs = Call("inf", Call("ker", n), Range(n, Sub(j, D(1))));
        var body = All("K", Type(), All("V", Type(),
            Assumption(Call("Field", k), Assumption(Call("AddCommGroup", v),
                Assumption(Call("Module", k, v), All("N", End(k, v),
                    All("j", Nat(), Eq(CAt(n, j), rhs))))))));
        return body;
    }

    private static Formula BlockCountDefinition()
    {
        var k = F.Id("K"); var v = F.Id("V"); var n = F.Id("N"); var j = F.Id("j");
        var quotient = Call("quotient", CAt(n, j),
            Call("comap", Call("subtype", CAt(n, j)), CAt(n, Add(j, D(1)))));
        var body = All("K", Type(), All("V", Type(),
            Assumption(Call("Field", k), Assumption(Call("AddCommGroup", v),
                Assumption(Call("Module", k, v), Assumption(Call("FiniteDimensional", k, v),
                    All("N", End(k, v), All("j", Nat(),
                        Eq(Call("blockCount", n, j), Call("finrank", k, quotient))))))))));
        return body;
    }

    private static Formula RankFormula()
    {
        var k = F.Id("K"); var v = F.Id("V"); var n = F.Id("N"); var j = F.Id("j");
        var rhs = Add(Sub(CastInt(Rho(n, Sub(j, D(1)))),
            Mul(D(2), CastInt(Rho(n, j)))), CastInt(Rho(n, Add(j, D(1)))));
        var body = All("K", Type(), All("V", Type(),
            Assumption(Call("Field", k), Assumption(Call("AddCommGroup", v),
                Assumption(Call("Module", k, v), Assumption(Call("FiniteDimensional", k, v),
                    All("N", End(k, v), All("j", Nat(),
                        Implies(Le(D(1), j), Eq(CastInt(BlockAt(n, j)), rhs))))))))));
        return body;
    }

    private static Formula DeterminesCount()
    {
        var k = F.Id("K"); var v = F.Id("V"); var w = F.Id("W");
        var n = F.Id("N"); var nPrime = F.Id("Nprime"); var r = F.Id("r"); var j = F.Id("j");
        var equalRanks = All("r", Nat(), Eq(Rho(n, r), Rho(nPrime, r)));
        var conclusion = All("j", Nat(), Eq(BlockAt(n, j), BlockAt(nPrime, j)));
        var theorem = All("N", End(k, v), All("Nprime", End(k, w),
            Implies(equalRanks, conclusion)));
        var assumptions = Assumption(Call("Field", k),
            Assumption(Call("AddCommGroup", v),
                Assumption(Call("Module", k, v),
                    Assumption(Call("FiniteDimensional", k, v),
                        Assumption(Call("AddCommGroup", w),
                            Assumption(Call("Module", k, w),
                                Assumption(Call("FiniteDimensional", k, w), theorem)))))));
        return All("K", Type(), All("V", Type(), All("W", Type(), assumptions)));
    }
}
