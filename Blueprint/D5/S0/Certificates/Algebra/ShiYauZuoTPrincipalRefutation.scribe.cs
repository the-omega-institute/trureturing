using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates.Algebra;

internal sealed class ShiYauZuoTPrincipalRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/Algebra/ShiYauZuoTPrincipalRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/shiyauzuo2024tmaps");

    private static readonly Formula Field = F.Id("F"), Ring = F.Id("A"), Map = F.Id("Q");
    private static readonly Formula I = F.Id("I"), J = F.Id("J"), R = F.Id("r"), G = F.Id("g");
    private static readonly Formula N = F.Id("n"), Index = F.Id("i"), Component = F.Id("j");
    private static readonly Formula Type = Name("Type"), Prop = Name("Prop");
    private static readonly Formula Nat = Seq(Mathbb, Grp(F.Id("N")));
    private static readonly Formula Poly = App("MvPolynomial", App("Fin", R), Ring);
    private static readonly Formula TMap = App("TMap", Field, Ring);
    private static readonly Formula Ideal = App("Ideal", Ring);
    private static readonly Formula Tuple = Arrow(App("Fin", R), Ring);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A binary square-zero local algebra refutes Shi-Yau-Zuo Conjecture 4.79.",
        H("A finite-field counterexample to the T-principality criterion"),
        Blocks(
            Node("valueIdeal", "Ideal of component values", ValueIdealFormula(),
                "Definition 4.1 takes the ideal span of the values of a finite family of F-linear endomorphisms."),
            Node("TMap", "T-maps", TMapFormula(),
                "Definition 4.1 and Remark 4.3 keep the F-linear maps as data. The fields count and components specify their number and family. The field mul_le requires Q(af) ⊆ Q(f) for every a and f in A."),
            Node("imageIdeal", "Image ideal", ImageFormula(),
                "Definition 4.6 sums the value ideals over all elements of J. For generators of J it equals the sum of their value ideals, by linearity and the multiplication law."),
            Node("delta", "Ideal of antiderivatives", DeltaFormula(),
                "Definition 4.8 collects the elements whose value ideals are contained in I. Linearity and the multiplication law give the ideal operations, as in Remark 4.9."),
            Node("TPrincipal", "T-principality", PrincipalFormula(),
                "The paragraph after Example 4.5 calls I T-principal when it is the value ideal of one element."),
            Node("TFull", "T-fullness", FullFormula(),
                "Definition 4.66 requires the image of the antiderivative ideal to be I."),
            Node("genericElement", "Generic linear combination", GenericFormula(),
                "Definition 4.68 attaches one independent variable to each coefficient from the generating tuple."),
            Node("genericImage", "Coefficientwise image of the generic element", GenericImageFormula(),
                "The sum runs over the finitely supported coefficient function of the generic element. Each component acts on the coefficients and leaves the monomial exponents fixed. Its value on the generic element is the sum of Qⱼ(gᵢ) times Xᵢ, by additivity and preservation of zero."),
            Node("TDependent", "T-dependence by the polynomial colon", DependentFormula(),
                "Definition 4.68 tests a generating tuple by asking whether the colon of the generic image by the extended image ideal escapes the extended maximal ideal. Both extensions use the coefficient inclusion C into the polynomial ring of that tuple. The Lean predicate asks for at least one finite generating tuple satisfying this test."),
            Node("claim", "Conjecture 4.79", ClaimFormula(),
                "The conjecture is in §4.6, printed English p. 1217 and original-edition p. 222. The residue field is the native quotient by the maximal ideal. The hypothesis identifies it with F by an F-algebra equivalence, as used by the source's coefficient projection. The proposition includes both implications over an arbitrary field, with T-dependence read existentially."),
            Node("result", "Refutation of the arbitrary-field biconditional", Seq(Neg, Sp, Name("claim")),
                "Take A = TrivSqZeroExt (ZMod 2) (Fin 3 → ZMod 2). The scalar projection identifies the residue field with ZMod 2 as an algebra over ZMod 2. "
                    + "Its kernel I is the square-zero maximal ideal. Each component keeps the scalar part and places u, v, or u + v on its own axis. "
                    + "On I multiplication acts through the scalar part. Away from I the component values are units, so the T-map law holds. The three axes give Δ(I) = Q(I) = I. "
                    + "Every ideal-generating tuple of I spans it over ZMod 2. Applying the three coordinate forms to the generic combination gives three linear forms U, V, and U + V, each nonzero over the residue field. "
                    + "The actual generic image has generators C(e₀)U, C(e₁)V, and C(e₂)(U + V). Multiplication by the complementary factors of UV(U + V) puts the product times each extended axis in the generic image. "
                    + "The product survives coefficient reduction because the polynomial ring over ZMod 2 is a domain. This proves the colon test for every generating tuple. "
                    + "Every binary pair makes at least one of u, v, and u + v zero. Scalar multiplication preserves the missing coordinate, and a unit gives the whole ring. Thus I is never a value ideal. "
                    + "The finite example refutes sufficiency for a chosen tuple, an existential tuple, and the reading that every tuple must pass. The infinite-field biconditional in Theorem 4.76 holds with the existential tuple reading.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("shi-yau-zuo-t-principal-4-79"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Definition, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("shi-yau-zuo-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            role == DescribeRole.Theorem ? AssessedProvenance.FromRepo(Source) : AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Name(string name) => Seq(Operatorname,
        Grp(Seq([.. name.Split('.').SelectMany((part, index) =>
            index == 0 ? new[] { F.Id(part) } : new[] { Dot, F.Id(part) })])));
    private static Formula App(string name, params Formula[] args) => Apply(Name(name), args);
    private static Formula Apply(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parens(Formula content) => Seq(Open, content, Close);
    private static Formula Typed(Formula value, Formula type) => Seq(value, Sp, Colon, Sp, type);
    private static Formula Implicit(Formula value, Formula type) => Seq(OpenBrace, Typed(value, type), CloseBrace);
    private static Formula Instance(string name, params Formula[] args) => Seq(OpenBracket, App(name, args), CloseBracket);
    private static Formula Arrow(Formula input, Formula output) => Seq(input, Sp, To, Sp, output);
    private static Formula EqualTo(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula AtMost(Formula left, Formula right) => Seq(left, Sp, Le, Sp, right);
    private static Formula All(Formula parameters, Formula body) => Seq(Forall, Sp, parameters, Comma, Sp, body);
    private static Formula Some(Formula parameters, Formula body) => Seq(Exists, Sp, parameters, Comma, Sp, body);
    private static Formula LambdaOf(Formula parameters, Formula body) => Seq(LambdaLower, Sp, parameters, Comma, Sp, body);

    private static Formula AlgebraParameters(bool implicitCarriers) => Seq(
        implicitCarriers ? Implicit(Field, Type) : Parens(Typed(Field, Type)), Sp, Instance("Field", Field), Sp,
        implicitCarriers ? Implicit(Ring, Type) : Parens(Typed(Ring, Type)), Sp,
        Instance("CommRing", Ring), Sp, Instance("Algebra", Field, Ring));
    private static Formula MapParameters() => Seq(AlgebraParameters(true), Sp, Parens(Typed(Map, TMap)));
    private static Formula Values(Formula x) => App("valueIdeal", App("TMap.components", Map), x);
    private static Formula ComponentFamily(Formula count) =>
        Arrow(App("Fin", count), Seq(Ring, Sp, To,
            Underscore, Grp(Seq(F.Id("l"), OpenBracket, Field, CloseBracket)), Sp, Ring));

    private static Formula ValueIdealFormula()
    {
        Formula family = F.Id("components"), x = F.Id("f");
        Formula generators = App("Set.range", LambdaOf(Component, Apply(family, Component, x)));
        return All(Seq(AlgebraParameters(true), Sp, Implicit(N, Nat), Sp,
                Parens(Typed(family, ComponentFamily(N))), Sp, Parens(Typed(x, Ring))),
            EqualTo(Typed(App("valueIdeal", family, x), Ideal), App("Ideal.span", generators)));
    }

    private static Formula TMapFormula()
    {
        Formula x = F.Id("f"), a = F.Id("a"), count = Name("count"), family = Name("components");
        Formula law = All(Typed(Seq(a, Sp, x), Ring),
            AtMost(App("valueIdeal", family, Seq(a, Sp, Cdot, Sp, x)), App("valueIdeal", family, x)));
        return All(AlgebraParameters(false),
            Seq(Typed(TMap, Type), Quad, OpenBrace, Typed(count, Nat), Comma, Sp,
                Typed(family, ComponentFamily(count)), Comma, Sp,
                Typed(Seq(Name("mul"), Underscore, Grp(Name("le"))), law), CloseBrace));
    }

    private static Formula ImageFormula()
    {
        Formula x = F.Id("f");
        return All(Seq(MapParameters(), Sp, Parens(Typed(J, Ideal))),
            EqualTo(Typed(App("imageIdeal", Map, J), Ideal),
                App("sSup", Seq(OpenBrace, Values(x), Sp, Mid, Sp, x, Sp, InMacro, Sp, J, CloseBrace))));
    }

    private static Formula DeltaFormula()
    {
        Formula x = F.Id("f");
        return All(Seq(MapParameters(), Sp, Parens(Typed(I, Ideal))),
            EqualTo(Typed(App("delta", Map, I), Ideal),
                Seq(OpenBrace, Typed(x, Ring), Sp, Mid, Sp, AtMost(Values(x), I), CloseBrace)));
    }

    private static Formula PrincipalFormula()
    {
        Formula x = F.Id("f");
        return All(Seq(MapParameters(), Sp, Parens(Typed(I, Ideal))),
            Seq(App("TPrincipal", Map, I), Sp, Iff, Sp, Some(Typed(x, Ring), EqualTo(I, Values(x)))));
    }

    private static Formula FullFormula() =>
        All(Seq(MapParameters(), Sp, Parens(Typed(I, Ideal))),
            Seq(App("TFull", Map, I), Sp, Iff, Sp, EqualTo(App("imageIdeal", Map, App("delta", Map, I)), I)));

    private static Formula GenericFormula() =>
        All(Seq(Implicit(Ring, Type), Sp, Instance("CommRing", Ring), Sp, Implicit(R, Nat), Sp, Parens(Typed(G, Tuple))),
            EqualTo(Typed(App("genericElement", G), Poly),
                Seq(Sum, Underscore, Grp(Typed(Index, App("Fin", R))), Sp,
                    App("MvPolynomial.C", Apply(G, Index)), Sp, App("MvPolynomial.X", Index))));

    private static Formula GenericImageFormula()
    {
        Formula exponent = F.Id("d"), coefficient = F.Id("a");
        Formula coeffs = App("AddMonoidAlgebra.coeff", App("genericElement", G));
        Formula term = App("MvPolynomial.monomial", exponent,
            App("TMap.components", Map, Component, coefficient));
        Formula generator = App("Finsupp.sum", coeffs, LambdaOf(Seq(exponent, Sp, coefficient), term));
        return All(Seq(AlgebraParameters(true), Sp, Implicit(R, Nat), Sp,
                Parens(Typed(Map, TMap)), Sp, Parens(Typed(G, Tuple))),
            EqualTo(Typed(App("genericImage", Map, G), App("Ideal", Poly)),
                App("Ideal.span", App("Set.range", LambdaOf(Component, generator)))));
    }

    private static Formula DependentFormula()
    {
        Formula ringHom = Seq(Ring, Sp, To, Caret, Grp(Seq(Plus, Star)), Sp, Poly);
        Formula inclusion = Parens(Typed(Name("MvPolynomial.C"), ringHom));
        Formula imageExtension = App("Ideal.map", inclusion, App("imageIdeal", Map, J));
        Formula maximalExtension = App("Ideal.map", inclusion, App("IsLocalRing.maximalIdeal", Ring));
        Formula colon = App("Submodule.colon", App("genericImage", Map, G),
            Parens(Typed(App("SetLike.coe", imageExtension), App("Set", Poly))));
        Formula condition = Seq(EqualTo(App("Ideal.span", App("Set.range", G)), J),
            Sp, Land, Sp, Neg, Sp, Parens(AtMost(colon, maximalExtension)));
        return All(Seq(AlgebraParameters(true), Sp, Instance("IsLocalRing", Ring), Sp,
                Parens(Typed(Map, TMap)), Sp, Parens(Typed(J, Ideal))),
            Seq(App("TDependent", Map, J), Sp, Iff, Sp,
                Some(Seq(Parens(Typed(R, Nat)), Sp, Parens(Typed(G, Tuple))), condition)));
    }

    private static Formula ClaimFormula()
    {
        Formula residue = Seq(App("IsLocalRing.ResidueField", Ring), Sp, SimeqAlgebra(), Sp, Field);
        Formula conclusion = Seq(App("TPrincipal", Map, I), Sp, Iff, Sp, App("TFull", Map, I),
            Sp, Land, Sp, App("TDependent", Map, App("delta", Map, I)));
        Formula body = All(Seq(AlgebraParameters(false), Sp, Instance("IsLocalRing", Ring), Sp,
                Instance("IsNoetherianRing", Ring)),
            Arrow(App("Nonempty", residue),
                All(Seq(Parens(Typed(Map, TMap)), Sp, Parens(Typed(I, Ideal))), conclusion)));
        return EqualTo(Typed(Name("claim"), Prop), Parens(body));
    }

    private static Formula SimeqAlgebra() => Seq(Sim, Underscore, Grp(Seq(Name("Alg"), OpenBracket, Field, CloseBracket)));
}
