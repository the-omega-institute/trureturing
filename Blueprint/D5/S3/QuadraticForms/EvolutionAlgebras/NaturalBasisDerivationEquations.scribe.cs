using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms.EvolutionAlgebras;

internal sealed class NaturalBasisDerivationEquationsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuadraticForms/EvolutionAlgebras/NaturalBasisDerivationEquations.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical natural-basis equations for actual evolution derivations.",
        H("Natural-basis derivation equations"),
        Blocks(
            Paragraph(Text("These are the original canonical proof bodies factored from NondegenerateDerivationBlocks. Their qualified mathematical names and hypotheses are preserved. The ambient product is bilinear over an arbitrary field and its actual natural basis has zero mixed products; no associativity, unit or perfectness is assumed. For the normalized statements, label records the natural-square class and w its representative. The exact hypotheses concerning normalized squares, nonzero representatives and separation of distinct classes appear in each statement. Semisimple implications retain that explicit assumption. The scientific application retains Haobo Ma then Wenlin Zhang credit, alongside the classical linear and Lie ingredients; no priority claim is made.")),
            Entry("mul_basis_right", "Right multiplication in a natural basis",
                "For any finite natural basis, mu(x,b(j)) is the j-th coordinate of x times the square of b(j). Expanding x removes the mixed products."),
            Entry("mul_basis_left", "Left multiplication in a natural basis",
                "For any finite natural basis, mu(b(i),x) is the i-th coordinate of x times the square of b(i). Commutativity is not needed for this basis expansion."),
            Entry("square_equation", "The exact square derivation equation",
                "Every actual derivation sends the square of b(i) to twice its i-th diagonal coefficient times that square. This uses only bilinearity and the finite natural-basis equations."),
            Entry("separate_of_distinct_lines", "Distinct nonzero lines are independent",
                "Two nonzero vectors spanning different lines have no nontrivial two-term linear relation over the field. This is the original linear separation proof."),
            Entry("derivation_cross_zero", "Zero coefficients between distinct classes",
                "For normalized natural squares with separated representative lines, every actual derivation has zero coefficients between different label classes. Nonzero-representative and semisimplicity assumptions are not needed for this implication beyond the stated separation law."),
            Entry("derivation_off_diagonal_skew", "Skew off-diagonal coefficients",
                "With normalized nonzero square representatives and separated distinct classes, the off-diagonal coefficients of every actual derivation are skew. The diagonal coefficients are not asserted to vanish."),
            Entry("derivation_diagonal_eq_on_class", "Constant diagonal within one class",
                "In characteristic zero, two natural basis indices with the same normalized nonzero square have equal diagonal coefficients under every actual derivation. Class separation and semisimplicity are not hypotheses of this equality."),
            Entry("derivation_bracket_diagonal_zero", "Commutators have zero diagonal",
                "Under the normalized nonzero-square and class-separation hypotheses, the actual commutator of any two derivations has zero diagonal in the natural basis. This makes the diagonal map a Lie map to the abelian coordinate algebra."),
            Entry("semisimple_diagonal_zero", "The semisimple diagonal implication",
                "If the actual derivation algebra is semisimple, its perfectness and the zero commutator diagonal imply that each actual derivation has zero diagonal. The semisimplicity hypothesis is retained."),
            Entry("properties_of_diagonal_zero", "The exact zero-diagonal consequences",
                "An actual derivation with zero diagonal has zero cross-class coefficients, fully skew coefficients and annihilates every representative whose label occurs. This statement assumes zero diagonal directly and does not assume semisimplicity."),
            Entry("derivation_of_skew_killing", "Converse from skew coefficients and killed squares",
                "For normalized natural squares, any linear endomorphism with zero cross-class coefficients, skew coefficients and zero action on the occurring square representatives is an actual derivation. This converse needs neither nonzero representatives, class separation nor semisimplicity."),
            Entry("semisimple_normalized_derivation_iff", "The preserved semisimple equivalence",
                "The original semisimple-only equivalence identifies actual derivations with the zero-cross-class, skew, representative-killing conditions. It retains every original hypothesis and is separate from the new arbitrary-Ann0 radical-quotient theorem."),
            Entry("diagonalHom", "The actual diagonal Lie map",
                "The map sends an actual derivation to its natural-basis diagonal coefficients. Its target has the scalar commutator, which is zero. The proved zero diagonal of brackets verifies the Lie-map law without a semisimplicity hypothesis.", DescribeRole.Definition),
            Entry("skew_iff_coefficients", "Standard-form skew adjoints in coordinates",
                "For the actual standard symmetric form on a finite coordinate space, an endomorphism is skew adjoint exactly when its basis coefficients are skew. The proof checks the bilinear identity on the canonical coordinate basis; it is reused unchanged by the block constructions."))));

    private static DocumentBlock.Describe Entry(string name, string title, string text,
        DescribeRole role = DescribeRole.Theorem) => Describe.Lean(
        DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(Statement(name))),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), role);

    private static Formula Statement(string name)
    {
        var d = X("D"); var i = X("i"); var j = X("j"); var x = X("x");
        var bi = App(X("b"), i); var bj = App(X("b"), j);
        var square = App(Mu, bi, bi);
        Formula Derivation() => All(d, Der, name switch
        {
            "square_equation" => All(i, Iota,
                Eq(App(d, square), Smul(Mul(D(2), Coeff(d, i, i)), square))),
            "derivation_cross_zero" => All(i, Iota, All(j, Iota,
                Imp(Ne(App(Label, i), App(Label, j)), Eq(Coeff(d, i, j), D(0))))),
            "derivation_off_diagonal_skew" => All(i, Iota, All(j, Iota,
                Imp(Ne(i, j), Eq(Coeff(d, i, j), Neg(Coeff(d, j, i)))))),
            "derivation_diagonal_eq_on_class" => All(i, Iota, All(j, Iota,
                Imp(Eq(App(Label, i), App(Label, j)), Eq(Coeff(d, i, i), Coeff(d, j, j))))),
            "derivation_bracket_diagonal_zero" => All(X("E"), Der, All(i, Iota,
                Eq(Coeff(Call("Bracket.bracket", d, X("E")), i, i), D(0)))),
            "semisimple_diagonal_zero" => All(i, Iota, Eq(Coeff(d, i, i), D(0))),
            _ => Imp(All(i, Iota, Eq(Coeff(d, i, i), D(0))), Conditions(d))
        });
        return name switch
        {
            "mul_basis_right" => BasisContext(Imp(Natural, All(x, X("V"), All(j, Iota,
                Eq(App(Mu, x, bj), Smul(App(Call("Module.Basis.repr", X("b")), x, j), App(Mu, bj, bj))))))),
            "mul_basis_left" => BasisContext(Imp(Natural, All(x, X("V"), All(i, Iota,
                Eq(App(Mu, bi, x), Smul(App(Call("Module.Basis.repr", X("b")), x, i), square)))))),
            "square_equation" => BasisContext(Imp(Natural, Derivation())),
            "separate_of_distinct_lines" => SeparationFormula(),
            "derivation_cross_zero" => NormalizedContext(Derivation(), false, true),
            "derivation_off_diagonal_skew" or "derivation_bracket_diagonal_zero" or
                "properties_of_diagonal_zero" => NormalizedContext(Derivation(), true, true),
            "derivation_diagonal_eq_on_class" => NormalizedContext(Derivation(), true, false, characteristicZero: true),
            "semisimple_diagonal_zero" => NormalizedContext(
                Instance(Call("LieAlgebra.IsSemisimple", X("k"), Der), Derivation()), true, true),
            "derivation_of_skew_killing" => NormalizedContext(All(d, End(X("V")),
                Imp(Conditions(d), Member(d, Der))), false, false),
            "semisimple_normalized_derivation_iff" => NormalizedContext(
                Instance(Call("LieAlgebra.IsSemisimple", X("k"), Der), All(d, End(X("V")),
                    new Formula.Logic(Member(d, Der), FormulaLogicOperator.Iff, Conditions(d)))), true, true),
            "diagonalHom" => NormalizedContext(
                And(Seq(Call("Normalized.diagonalHom", Mu, X("b"), Label, W), Sp, Colon, Sp,
                        Call("LieHom", X("k"), Der, new Formula.TypeArrow(Iota, X("k")))),
                    All(d, Der, All(i, Iota,
                        Eq(App(Call("Normalized.diagonalHom", Mu, X("b"), Label, W), d, i), Coeff(d, i, i))))), true, true),
            _ => SkewFormula()
        };
    }

    private static Formula SeparationFormula()
    {
        var x = X("x"); var y = X("y"); var s = X("s"); var t = X("t");
        Formula body = Imp(Eq(Add(Smul(s, x), Smul(t, y)), D(0)), And(Eq(s, D(0)), Eq(t, D(0))));
        body = All(s, X("k"), All(t, X("k"), body));
        body = Imp(Ne(Call("Submodule.span", X("k"), Call("Set.singleton", x)), Call("Submodule.span", X("k"), Call("Set.singleton", y))), body);
        return AlgebraContext(All(x, X("V"), All(y, X("V"), Imp(Ne(x, D(0)), Imp(Ne(y, D(0)), body)))));
    }

    private static Formula SkewFormula()
    {
        var d = X("D"); var i = X("i"); var j = X("j");
        var v = new Formula.TypeArrow(Iota, X("k"));
        Formula body = new Formula.Logic(Call("LinearMap.BilinForm.IsSkewAdjoint",
                MatrixForm, d),
            FormulaLogicOperator.Iff, All(i, Iota, All(j, Iota,
                Eq(App(d, Call("Pi.single", i, D(1)), j), Neg(App(d, Call("Pi.single", j, D(1)), i))))));
        return All(X("k"), Type, Instance(Call("Field", X("k")), All(Iota, Type,
            Instance(Call("Fintype", Iota), Instance(Call("DecidableEq", Iota), All(d, End(v), body))))));
    }

    private static Formula Conditions(Formula d) => And(
        All(X("i"), Iota, All(X("j"), Iota,
            Imp(Ne(App(Label, X("i")), App(Label, X("j"))), Eq(Coeff(d, X("i"), X("j")), D(0))))),
        And(All(X("i"), Iota, All(X("j"), Iota,
                Eq(Coeff(d, X("i"), X("j")), Neg(Coeff(d, X("j"), X("i")))))),
            All(X("a"), X("alpha"), Imp(Member(X("a"), Call("Set.range", Label)),
                Eq(App(d, App(W, X("a"))), D(0))))));

    private static Formula NormalizedContext(Formula body, bool nonzero, bool separated,
        bool characteristicZero = false)
    {
        if (separated)
            body = Imp(All(X("a"), X("alpha"), All(X("c"), X("alpha"),
                Imp(Ne(X("a"), X("c")), All(X("s"), X("k"), All(X("t"), X("k"),
                    Imp(Eq(Add(Smul(X("s"), App(W, X("a"))), Smul(X("t"), App(W, X("c")))), D(0)),
                        And(Eq(X("s"), D(0)), Eq(X("t"), D(0))))))))), body);
        if (nonzero) body = Imp(All(X("a"), X("alpha"), Ne(App(W, X("a")), D(0))), body);
        body = Imp(All(X("i"), Iota, Eq(App(Mu, App(X("b"), X("i")), App(X("b"), X("i"))),
            App(W, App(Label, X("i"))))), body);
        body = Imp(Natural, body);
        body = All(X("alpha"), Type, All(Label, new Formula.TypeArrow(Iota, X("alpha")),
            All(W, new Formula.TypeArrow(X("alpha"), X("V")), body)));
        if (characteristicZero) body = Instance(Call("CharZero", X("k")), body);
        return BasisContext(body);
    }

    private static Formula BasisContext(Formula body) => AlgebraContext(All(Mu,
        Call("LinearMap", X("k"), X("V"), Call("LinearMap", X("k"), X("V"), X("V"))),
        All(Iota, Type, Instance(Call("Fintype", Iota),
            All(X("b"), Call("Module.Basis", Iota, X("k"), X("V")), body)))));
    private static Formula AlgebraContext(Formula body) => All(X("k"), Type,
        Instance(Call("Field", X("k")), All(X("V"), Type,
            Instance(Call("AddCommGroup", X("V")), Instance(Call("Module", X("k"), X("V")), body)))));
    private static Formula Natural => All(X("i"), Iota, All(X("j"), Iota,
        Imp(Ne(X("i"), X("j")), Eq(App(Mu, App(X("b"), X("i")), App(X("b"), X("j"))), D(0)))));
    private static Formula Coeff(Formula d, Formula i, Formula j) => App(Call("Module.Basis.repr", X("b")), App(d, App(X("b"), i)), j);
    private static Formula Der => Call("derivations", Mu);
    private static Formula End(Formula v) => Call("Module.End", X("k"), v);
    private static Formula X(string s) => F.Id(s);
    private static Formula Type => Call("Type");
    private static Formula Mu => X("mu");
    private static Formula Iota => X("I");
    private static Formula Label => X("label");
    private static Formula W => X("w");
    private static Formula MatrixForm => App(Seq(Call("Matrix"), Dot,
        new Formula.Subscript(Call("toLinearMap"), D(2)), Apos), X("k"),
        Seq(D(1), Sp, Colon, Sp, Call("Matrix", Iota, Iota, X("k"))));
    private static Formula App(Formula f, params Formula[] xs) => new Formula.Apply(f, [.. xs]);
    private static Formula Call(string s, params Formula[] xs) => App(Seq(s.Split('.').SelectMany((part, i) =>
        i == 0 ? new Formula[] { Seq(Operatorname, Grp(X(part))) } :
            new Formula[] { Dot, Seq(Operatorname, Grp(X(part))) }).ToArray()), xs);
    private static Formula All(Formula x, Formula t, Formula b) => Seq(Forall, Sp, Open, x, Sp, Colon, Sp, t, Close, Comma, Sp, Open, b, Close);
    private static Formula Instance(Formula t, Formula b) => Seq(OpenBracket, t, CloseBracket, Sp, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Neg(Formula a) => Seq(Minus, a);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Smul(Formula a, Formula b) => Call("smul", a, b);
}
