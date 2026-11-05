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
                "The actual simple-ideal classification and the literal Serre G2 exclusion are stated separately below."))),
                DescribeRole.Theorem),
            Entry("simple_ideal_type", "Every actual nonabelian simple ideal", IdealContext(SimpleType()),
                "Every actual nonabelian simple Lie ideal of the actual derivation algebra is Lie equivalent to standard so3 or to so_m for m at least five. A solvable kernel cannot contain a nonzero simple ideal. A nonzero coordinate projection has ideal image because the full map is surjective; simplicity of the coordinate then gives the equivalence. If that coordinate has size four, the proved actual so4 equivalence with so3 times so3 supplies a nonzero size-three projection. This concerns ideals, not arbitrary subalgebras or faithful actions."),
            Entry("simple_ideal_not_sl3", "Exclusion of actual sl3", IdealContext(Excluded(Call("SpecialLinear.sl", Call("Fin", D(3)), X("k")))),
                "No such simple ideal is Lie equivalent to the actual standard special linear algebra sl3. Its proved dimension eight is not m choose two for any m. The simple-ideal type theorem supplies an actual orthogonal equivalence before the dimension argument."),
            Entry("simple_ideal_not_g2", "Exclusion of the actual Serre G2", IdealContext(Excluded(G2)),
                "The target is literally mathlib's LieAlgebra.g₂ k, defined by the G2 Cartan matrix and Serre relations. The companion SerreG2MatrixImage source constructs a surjection from this actual object to a proved fourteen-dimensional matrix image. A hypothetical ideal equivalence transports simplicity to the Serre object, so its nonzero surjection is injective and gives a proved correspondence. Fourteen is not m choose two. No unconditional Serre dimension theorem, assumed equivalence or dimension-tagged proxy is used."))));

    private static DocumentBlock.Describe Entry(string name, string title, Formula formula, string text) =>
        Describe.Lean(DescribeId.Create(name.Replace('_','-').ToLowerInvariant()), DeclarationHandle.Create(
            "D5/S3/QuadraticForms/EvolutionAlgebras/DerivationRadicalQuotient." + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
    private static Formula G2 => App(Seq(Qualified("LieAlgebra"), Dot,
        new Formula.Subscript(Seq(Operatorname, Grp(X("g"))), D(2))), X("k"));
    private static Formula Der => Call("derivations", X("mu"));
    private static Formula SimpleType() => Some(X("m"), Call("Nat"), And(
        new Formula.Logic(Eq(X("m"), D(3)), FormulaLogicOperator.Or,
            new Formula.Relation(D(5), FormulaRelationOperator.LessThanOrEqual, X("m"))),
        Call("Nonempty", Call("LieEquiv", X("k"), X("I"),
            Call("LieAlgebra.Orthogonal.so", Call("Fin", X("m")), X("k"))))));
    private static Formula Excluded(Formula target) => Seq(Neg, Call("Nonempty",
        Call("LieEquiv", X("k"), X("I"), target)));
    private static Formula Domain(Formula body)
    {
        body = Imp(Eq(Call("LinearMap.ker", X("mu")), Call("bot")), body);
        body = Imp(Call("IsEvolutionAlgebra", X("mu")), body);
        body = All(X("mu"), Call("LinearMap", X("k"), X("V"), Call("LinearMap", X("k"), X("V"), X("V"))), body);
        body = Instance(Call("FiniteDimensional", X("k"), X("V")), body);
        body = Instance(Call("Module", X("k"), X("V")), body);
        body = Instance(Call("AddCommGroup", X("V")), body);
        body = All(X("V"), Call("Type"), body);
        body = Instance(Call("CharZero", X("k")), body);
        body = Instance(Call("IsAlgClosed", X("k")), body);
        body = Instance(Call("Field", X("k")), body);
        return All(X("k"), Call("Type"), body);
    }
    private static Formula IdealContext(Formula body) => Domain(All(X("I"),
        Call("LieIdeal", X("k"), Der), Instance(Call("LieAlgebra.IsSimple", X("k"), X("I")), body)));
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
