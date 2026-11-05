using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HilbertOperators;

internal sealed class DavisKahanProjectorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/HilbertOperators/DavisKahanProjector.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/leanpool2026daviskahanprojector");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coercive Sylvester estimates and the common-gap Davis--Kahan projector bound over arbitrary complete real or complex Hilbert spaces.",
        H("Common-gap stability of orthogonal projectors"),
        Blocks(
            Paragraph(Text("The scalar k has an RCLike structure, including the real and complex fields. ContinuousLinearMap(k,E,F) denotes bounded continuous k-linear maps from E to F; LinearMap(k,E,F) denotes algebraic k-linear maps. Every norm of a continuous linear map is its operator norm; vector norms are the given Hilbert norms. Inner products use the displayed scalar k, and re takes their real part. All displayed variables and typeclass assumptions are quantified.")),
            Paragraph(Text("For a projectable submodule U, P(U) denotes U.starProjection, the orthogonal projector regarded as a bounded endomorphism of the ambient space. Orthogonal(U) is U's orthogonal complement. Comp denotes continuous-linear-map composition and agrees with multiplication of endomorphisms; the numeral one denotes the identity endomorphism. Real scalars in k-linear expressions use the canonical RCLike real embedding.")),
            Paragraph(Text("The full projector theorem allows arbitrary dimension, including zero-dimensional and infinite-dimensional ambient spaces, and zero, whole, or coincident subspaces. It assumes no equal-rank, finite-rank, simple-eigenvalue, operator-positivity, nonzero-subspace, or small-perturbation condition. The four quadratic-form bounds use the same real c and positive gap g. These are conditional form estimates; no spectral-measure or spectral-support conversion is asserted.")),
            Entry("rayleigh-norm-bound", "norm_le_of_abs_re_inner_map_self_le", RayleighFormula(),
                "TauCeti.ContinuousLinearMap.norm_le_of_abs_re_inner_map_self_le bounds a symmetric operator by its real quadratic form. Completeness is absent. The private correction-operator estimate norm_opNorm_smul_one_sub_le uses it in the Sylvester absorption argument."),
            Entry("rectangular-coercive-sylvester", "le_div_of_comp_add_comp_eq_rectangular", SylvesterFormula(false),
                "TauCeti.ContinuousLinearMap.le_div_of_comp_add_comp_eq_rectangular bounds an arbitrary rectangular solution of A composed with X plus X composed with B equals Y. The real-valued functional N is subadditive, exactly homogeneous in the scalar norm, and bounded under left and right multiplication by the operator norm. No definiteness, completeness, equal carrier, or nonzero-solution assumption is imposed. The zero solution is treated separately. Correction operators yield absorption by twice the positive coercivity delta."),
            Entry("rectangular-separated-sylvester", "le_div_of_comp_sub_comp_eq_rectangular", SylvesterFormula(true),
                "TauCeti.ContinuousLinearMap.le_div_of_comp_sub_comp_eq_rectangular applies the preceding estimate after shifting at the midpoint c plus g divided by two. The upper bound for B is c and the lower bound for A is c plus g. All four assumptions on the rectangular functional N remain explicit."),
            Entry("operator-norm-sylvester", "opNorm_le_div_of_comp_sub_comp_eq", OperatorSylvesterFormula(),
                "TauCeti.ContinuousLinearMap.opNorm_le_div_of_comp_sub_comp_eq specializes the separated rectangular estimate to the operator norm. The source and target are independently quantified normed inner-product spaces over the same k, without completeness assumptions."),
            Entry("reduced-extension-form", "re_inner_reducedExtension_self", ReducedFormula(),
                "TauCeti.re_inner_reducedExtension_self splits the real quadratic form of a linear map on a projectable invariant subspace and a scalar action on its orthogonal complement. The map R is algebraic, need not be bounded or symmetric, and needs invariance only on W. The private bounded-map version re_inner_bounded_reducedExtension_self applies this identity to the reduced extensions in Submodule.sinTheta_directed_coercive."),
            Entry("orthogonal-block-norm", "norm_add_eq_max_of_block", BlockFormula(),
                "ContinuousLinearMap.norm_add_eq_max_of_block gives the exact maximum of the norms of two complementary supported blocks. Its hypotheses include self-adjointness, idempotence, contraction of P and one minus P, and all four left/right support equations. The Pythagorean split controls the upper bound and the support equations recover both lower bounds."),
            Entry("two-projection-maximum", "norm_starProjection_sub_eq_max", ProjectionMaxFormula(),
                "Submodule.norm_starProjection_sub_eq_max expresses the symmetric projector distance as the maximum of its two directed cross-projection norms. It uses ContinuousLinearMap.norm_add_eq_max_of_block and the C-star norm identities. It requires no rank or nonzero-subspace restriction."),
            Entry("directed-coercive-angle", "sinTheta_directed_coercive", DirectedFormula(),
                "Submodule.sinTheta_directed_coercive forms reduced extensions on U and V. The two operators preserve their respective subspaces and orthogonal complements. Projection commutation gives a Sylvester equation for the cross projection, and perturbation compression bounds its forcing term by the norm of B minus A. Only the lower form bound on U and the upper form bound on V are required here."),
            Entry("common-gap-projector-bound", "opNorm_starProjection_sub_le_of_coercive", EndpointFormula(),
                "Submodule.opNorm_starProjection_sub_le_of_coercive is the common-gap projector theorem. Apply Submodule.sinTheta_directed_coercive to U and the orthogonal complement of W, then to W and the orthogonal complement of U, and combine the two estimates with Submodule.norm_starProjection_sub_eq_max. The constant is one, with denominator g."))));

    private static DocumentBlock Entry(string id, string name, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(name),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(V(name)), Open };
        for (var index = 0; index < args.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(args[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Par(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Inst(Formula type) => Seq(OpenBracket, type, CloseBracket, Sp);
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Map(string source, string target) =>
        Call("ContinuousLinearMap", V("k"), V(source), V(target));
    private static Formula Subspace(string space) => Call("Submodule", V("k"), V(space));
    private static Formula Fn(Formula source, Formula target) => Seq(Par(source), Sp, To, Sp, target);
    private static Formula Apply(string name, Formula x) => Seq(V(name), Par(x));
    private static Formula Norm(Formula x) => new Formula.Norm(x);
    private static Formula SqNorm(Formula x) => Seq(Norm(x), Caret, Grp(D(2)));
    private static Formula Add(Formula x, Formula y) => Seq(x, Sp, Plus, Sp, y);
    private static Formula Sub(Formula x, Formula y) => Seq(x, Sp, Minus, Sp, y);
    private static Formula Mul(Formula x, Formula y) => Seq(Par(x), Sp, Cdot, Sp, Par(y));
    private static Formula Eqn(Formula x, Formula y) => Seq(x, Sp, Eq, Sp, y);
    private static Formula Le(Formula x, Formula y) => Seq(x, Sp, Leq, Sp, y);
    private static Formula LtThan(Formula x, Formula y) => Seq(x, Sp, Lt, Sp, y);
    private static Formula Div(Formula x, Formula y) => Seq(Frac, Grp(x), Grp(y));
    private static Formula Imp(Formula hypothesis, Formula conclusion) =>
        Seq(Par(hypothesis), Sp, Rightarrow, Sp, conclusion);
    private static Formula And(params Formula[] values)
    {
        var items = new List<Formula>();
        foreach (var value in values)
        {
            if (items.Count > 0) items.AddRange([Sp, Land, Sp]);
            items.Add(Par(value));
        }
        return Seq([.. items]);
    }
    private static Formula Comp(Formula x, Formula y) => Seq(Par(x), Sp, Circ, Sp, Par(y));
    private static Formula P(string space) => Call("P", V(space));
    private static Formula Orth(string subspace) => Call("Orthogonal", V(subspace));
    private static Formula Member(Formula x, Formula space) => Seq(x, Sp, InMacro, Sp, space);
    private static Formula Sym(string op) => Call("IsSymmetric", V(op));
    private static Formula Form(string op, Formula x) =>
        Call("re", Seq(Langle, Sp, Apply(op, x), Comma, Sp, x, Sp, Rangle,
            Underscore, Grp(V("k"))));
    private static Formula Lower(string op, string space, Formula bound) =>
        All("x", V(space), Le(Mul(bound, SqNorm(V("x"))), Form(op, V("x"))));
    private static Formula Upper(string op, string space, Formula bound) =>
        All("x", V(space), Le(Form(op, V("x")), Mul(bound, SqNorm(V("x")))));
    private static Formula Restricted(string op, string space, Formula subspace, Formula bound, bool lower) =>
        All("x", V(space), Imp(Member(V("x"), subspace), lower
            ? Le(Mul(bound, SqNorm(V("x"))), Form(op, V("x")))
            : Le(Form(op, V("x")), Mul(bound, SqNorm(V("x"))))));
    private static Formula Invariant(string op, string space, Formula subspace) =>
        All("x", V(space), Imp(Member(V("x"), subspace), Member(Apply(op, V("x")), subspace)));
    private static Formula Reduces(string op, string space, string subspace) =>
        And(Invariant(op, space, V(subspace)), Invariant(op, space, Orth(subspace)));

    private static Formula Telescope(Formula body, bool complete, params string[] spaces)
    {
        var instances = new List<Formula> { Inst(Call("RCLike", V("k"))) };
        foreach (var space in spaces)
        {
            instances.Add(Inst(Call("NormedAddCommGroup", V(space))));
            instances.Add(Inst(Call("InnerProductSpace", V("k"), V(space))));
            if (complete) instances.Add(Inst(Call("CompleteSpace", V(space))));
        }
        instances.Add(body);
        body = Seq([.. instances]);
        for (var i = spaces.Length - 1; i >= 0; i--)
            body = All(spaces[i], Seq(Operatorname, Grp(V("Type")), Underscore, Grp(V(i == 0 ? "v" : "w"))), body);
        body = All("k", Seq(Operatorname, Grp(V("Type")), Underscore, Grp(V("u"))), body);
        if (spaces.Length == 2) body = All("w", Call("UniverseLevel"), body);
        return All("u", Call("UniverseLevel"), All("v", Call("UniverseLevel"), body));
    }
    private static Formula Projectable(string subspace) => Inst(Call("HasOrthogonalProjection", V(subspace)));
    private static Formula Operators(Formula body, string first, string second, string from, string to) =>
        All("A", Map(first, first), All("B", Map(second, second),
        All("X", Map(from, to), All("Y", Map(from, to), body))));
    private static Formula FunctionalLaws() => And(
        All("f", Map("E", "F"), All("h", Map("E", "F"),
            Le(Apply("N", Add(V("f"), V("h"))), Add(Apply("N", V("f")), Apply("N", V("h")))))),
        All("a", V("k"), All("f", Map("E", "F"),
            Eqn(Apply("N", Mul(V("a"), V("f"))), Mul(Norm(V("a")), Apply("N", V("f")))))),
        All("C", Map("F", "F"), All("f", Map("E", "F"),
            Le(Apply("N", Comp(V("C"), V("f"))), Mul(Norm(V("C")), Apply("N", V("f")))))),
        All("f", Map("E", "F"), All("C", Map("E", "E"),
            Le(Apply("N", Comp(V("f"), V("C"))), Mul(Apply("N", V("f")), Norm(V("C")))))));

    private static Formula RayleighFormula() => Telescope(
        All("C", Map("E", "E"), All("q", Real, Imp(And(Sym("C"), Le(D(0), V("q")),
            All("x", V("E"), Le(new Formula.Absolute(Form("C", V("x"))), Mul(V("q"), SqNorm(V("x")))))),
            Le(Norm(V("C")), V("q"))))), false, "E");
    private static Formula SylvesterFormula(bool separated)
    {
        var equation = Eqn(separated ? Sub(Comp(V("A"), V("X")), Comp(V("X"), V("B")))
            : Add(Comp(V("A"), V("X")), Comp(V("X"), V("B"))), V("Y"));
        var hypotheses = separated
            ? And(FunctionalLaws(), Sym("A"), Sym("B"), LtThan(D(0), V("g")),
                Lower("A", "F", Add(V("c"), V("g"))), Upper("B", "E", V("c")), equation)
            : And(FunctionalLaws(), Sym("A"), Sym("B"), LtThan(D(0), V("d")),
                Lower("A", "F", V("d")), Lower("B", "E", V("d")), equation);
        var body = Imp(hypotheses, Le(Apply("N", V("X")),
            Div(Apply("N", V("Y")), separated ? V("g") : Mul(D(2), V("d")))));
        body = separated ? All("c", Real, All("g", Real, body)) : All("d", Real, body);
        return Telescope(Operators(All("N", Fn(Map("E", "F"), Real), body),
            "F", "E", "E", "F"), false, "E", "F");
    }
    private static Formula OperatorSylvesterFormula() => Telescope(
        Operators(All("c", Real, All("g", Real, Imp(And(Sym("A"), Sym("B"), LtThan(D(0), V("g")),
            Lower("A", "E", Add(V("c"), V("g"))), Upper("B", "F", V("c")),
            Eqn(Sub(Comp(V("A"), V("X")), Comp(V("X"), V("B"))), V("Y"))),
            Le(Norm(V("X")), Div(Norm(V("Y")), V("g")))))),
            "E", "F", "F", "E"), false, "E", "F");
    private static Formula ReducedFormula()
    {
        var projected = Seq(P("W"), Par(V("x")));
        var residual = Sub(V("x"), projected);
        var extended = Add(Apply("R", projected), Mul(Call("ofReal", V("q")), residual));
        var left = Call("re", Seq(Langle, Sp, extended, Comma, Sp, V("x"), Sp,
            Rangle, Underscore, Grp(V("k"))));
        var right = Add(Form("R", projected), Mul(V("q"), SqNorm(residual)));
        var body = All("q", Real, All("x", V("E"),
            Imp(Invariant("R", "E", V("W")), Eqn(left, right))));
        return Telescope(All("R", Call("LinearMap", V("k"), V("E"), V("E")),
            All("W", Subspace("E"), Seq(Projectable("W"), body))), false, "E");
    }
    private static Formula BlockFormula() => Telescope(
        All("P", Map("E", "E"), All("A", Map("E", "E"), All("B", Map("E", "E"),
        Imp(And(Call("IsSelfAdjoint", V("P")), Call("IsIdempotentElem", V("P")),
            All("x", V("E"), Le(Norm(Apply("P", V("x"))), Norm(V("x")))),
            All("x", V("E"), Le(Norm(Seq(Par(Sub(D(1), V("P"))), Par(V("x")))), Norm(V("x")))),
            Eqn(Comp(V("A"), V("P")), V("A")), Eqn(Comp(V("P"), V("A")), V("A")),
            Eqn(Comp(V("B"), V("P")), D(0)), Eqn(Comp(V("P"), V("B")), D(0))),
            Eqn(Norm(Add(V("A"), V("B"))), Call("max", Norm(V("A")), Norm(V("B")))))))), true, "E");
    private static Formula ProjectionMaxFormula() => Telescope(
        All("U", Subspace("E"), All("V", Subspace("E"),
        Seq(Projectable("U"), Projectable("V"), Eqn(Norm(Sub(P("U"), P("V"))),
            Call("max", Norm(Comp(Sub(D(1), P("V")), P("U"))),
                Norm(Comp(Sub(D(1), P("U")), P("V")))))))), true, "E");
    private static Formula SubspaceTelescope(Formula body, string space, string second) =>
        Telescope(All("A", Map(space, space), All("B", Map(space, space),
            All("U", Subspace(space), All(second, Subspace(space),
                Seq(Projectable("U"), Projectable(second), All("c", Real, All("g", Real, body))))))),
            true, space);
    private static Formula DirectedFormula() => SubspaceTelescope(
        Imp(And(Sym("A"), Sym("B"), Reduces("A", "E", "U"), Reduces("B", "E", "V"),
            LtThan(D(0), V("g")), Restricted("A", "E", V("U"), Add(V("c"), V("g")), true),
            Restricted("B", "E", V("V"), V("c"), false)),
            Le(Norm(Comp(P("V"), P("U"))), Div(Norm(Sub(V("B"), V("A"))), V("g")))), "E", "V");
    private static Formula EndpointFormula() => SubspaceTelescope(
        Imp(And(Sym("A"), Sym("B"), Reduces("A", "H", "U"), Reduces("B", "H", "W"),
            LtThan(D(0), V("g")),
            Restricted("A", "H", V("U"), Add(V("c"), V("g")), true),
            Restricted("A", "H", Orth("U"), V("c"), false),
            Restricted("B", "H", V("W"), Add(V("c"), V("g")), true),
            Restricted("B", "H", Orth("W"), V("c"), false)),
            Le(Norm(Sub(P("U"), P("W"))), Div(Norm(Sub(V("B"), V("A"))), V("g")))), "H", "W");
}
