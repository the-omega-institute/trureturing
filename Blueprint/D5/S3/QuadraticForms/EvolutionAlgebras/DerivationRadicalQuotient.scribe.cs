using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms.EvolutionAlgebras;

internal sealed class DerivationRadicalQuotientDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The radical quotient of zero-annihilator evolution derivations.",
        H("Arbitrary zero-annihilator derivations"),
        Blocks(Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(
            "D5/S3/QuadraticForms/EvolutionAlgebras/DerivationRadicalQuotient.result"),
            H("Actual solvable-radical quotient"), StatementSource.FromAuthor(Disp(Result())),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                "Let k be any algebraically closed field of characteristic zero and let V be finite-dimensional. " +
                "For any bilinear commutative evolution multiplication with an actual natural basis and zero annihilator, " +
                "the actual derivation Lie algebra modulo its actual solvable radical is Lie equivalent to a finite direct " +
                "sum of standard orthogonal Lie algebras with all sizes at least three. The sum may be empty, including " +
                "when V is zero. No unit, associativity, perfectness, square-dimension or semisimplicity assumption is imposed. " +
                "The construction uses the scalar-corrected actions on the nondegenerate reductions of the orthogonal " +
                "complements of the block spans. The general stabilizer surjections have kernels with zero triple brackets; " +
                "their preimage together with the abelian diagonal part is solvable. The discarded factors of dimensions " +
                "zero and one vanish and the dimension-two factor is abelian. All retained factors have trivial radical, " +
                "including the actual split dimension-four case. The first isomorphism theorem therefore identifies the " +
                "kernel with the actual radical and gives the displayed quotient. This is the quotient part of Corollary 8 " +
                "of the supplied note by Haobo Ma, then Wenlin Zhang. Orthogonal structure and the radical facts are classical. " +
                "The nonabelian simple-ideal classification and genuine G2 exclusion are separate obligations.")),
                DescribeRole.Theorem)))));

    private static Formula Result()
    {
        var k = X("k"); var v = X("V"); var mu = X("mu");
        var der = Call("derivations", mu);
        var quotient = Call("Quotient", der, Call("LieAlgebra.radical", k, der));
        var r = X("r"); var a = X("a"); var m = X("m");
        var fin = Call("Fin", r);
        var sum = Call("DirectSum", fin,
            Seq(Open, X("fun"), Sp, a, Sp, Mapsto, Sp, Call("LieAlgebra.Orthogonal.so", Call("Fin", App(m, a)), k), Close));
        Formula result = Some(r, Call("Nat"), Some(m, new Formula.TypeArrow(fin, Call("Nat")),
            And(All(a, fin, new Formula.Relation(D(3), FormulaRelationOperator.LessThanOrEqual, App(m,a))),
                Call("Nonempty", Call("LieEquiv", k, quotient, sum)))));
        result = Imp(Eq(Call("LinearMap.ker", mu), Call("bot")), result);
        result = Imp(Call("IsEvolutionAlgebra", mu), result);
        result = All(mu, Call("LinearMap", k, v, Call("LinearMap", k, v, v)), result);
        result = Instance(Call("FiniteDimensional", k, v), result);
        result = Instance(Call("Module", k, v), result);
        result = Instance(Call("AddCommGroup", v), result);
        result = All(v, Call("Type"), result);
        result = Instance(Call("CharZero", k), result);
        result = Instance(Call("IsAlgClosed", k), result);
        result = Instance(Call("Field", k), result);
        return All(k, Call("Type"), result);
    }
    private static Formula X(string s) => F.Id(s);
    private static Formula Qualified(string s) => Seq(s.Split('.').SelectMany((part,i) =>
        i == 0 ? new Formula[] { Seq(Operatorname, Grp(X(part))) } :
            new Formula[] { Dot, Seq(Operatorname, Grp(X(part))) }).ToArray());
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(Qualified(s), [.. xs]);
    private static Formula App(Formula f, params Formula[] xs) => new Formula.Apply(f, [.. xs]);
    private static Formula All(Formula x, Formula t, Formula b) => Seq(Forall, Sp, Open, x, Sp, Colon, Sp, t, Close, Comma, Sp, Open, b, Close);
    private static Formula Some(Formula x, Formula t, Formula b) => Seq(Exists, Sp, Open, x, Sp, Colon, Sp, t, Close, Comma, Sp, Open, b, Close);
    private static Formula Instance(Formula t, Formula b) => Seq(OpenBracket, t, CloseBracket, Sp, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
}
