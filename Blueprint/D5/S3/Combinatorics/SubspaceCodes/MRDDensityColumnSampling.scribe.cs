using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SubspaceCodes;

internal sealed class MRDDensityColumnSamplingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnSampling.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGeometry/gruica2023mrdcolumnlimit");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed-field MRD density: sampling argument.", H("MRD density: Sampling"), Blocks(
            Node("imageCode", "Imagecode",
                All("K", Word("Type"), Seq(OpenBracket, Call("Field", X("K")), CloseBracket, Sp, All("D", Word("Type"), Seq(OpenBracket, Call("AddCommGroup", X("D")), CloseBracket, Sp, Seq(OpenBracket, Call("Module", X("K"), X("D")), CloseBracket, Sp, All("E", Word("Type"), Seq(OpenBracket, Call("AddCommGroup", X("E")), CloseBracket, Sp, Seq(OpenBracket, Call("Module", X("K"), X("E")), CloseBracket, Sp, All("f", SubtypeOf("f", Call("LinearMap", App(Q("RingHom", "id"), X("K")),  X("D"), X("E")), App(Q("Function", "Injective"), X("f"))), Equal(Call("val", Typed(Call("imageCode", X("f")), SubtypeOf("U", Call("Submodule", X("K"), X("E")), Equal(App(Q("Module", "finrank"), X("K"), X("U")), App(Q("Module", "finrank"), X("K"), X("D")))))), App(Q("LinearMap", "range"), Call("val", X("f"))))))))))))),
                DescribeRole.Definition, AssessedProvenance.FromRepo(),
                "The underlying subspace is the range of the injective linear map; its dimension equals that of the source."),
            Node("uniform_image_ratio", "Uniform image ratio",
                All("K", Word("Type"), Seq(OpenBracket, Call("Field", X("K")), CloseBracket, Sp, All("D", Word("Type"), Seq(OpenBracket, Call("AddCommGroup", X("D")), CloseBracket, Sp, Seq(OpenBracket, Call("Module", X("K"), X("D")), CloseBracket, Sp, Seq(OpenBracket, Call("FiniteDimensional", X("K"), X("D")), CloseBracket, Sp, All("E", Word("Type"), Seq(OpenBracket, Call("AddCommGroup", X("E")), CloseBracket, Sp, Seq(OpenBracket, Call("Module", X("K"), X("E")), CloseBracket, Sp, Seq(OpenBracket, Call("FiniteDimensional", X("K"), X("E")), CloseBracket, Sp, Seq(OpenBracket, Call("Finite", X("K")), CloseBracket, Sp, Seq(OpenBracket, Call("Finite", X("D")), CloseBracket, Sp, Seq(OpenBracket, Call("Finite", X("E")), CloseBracket, Sp, All("P", Arrow(SubtypeOf("U", Call("Submodule", X("K"), X("E")), Equal(App(Q("Module", "finrank"), X("K"), X("U")), App(Q("Module", "finrank"), X("K"), X("D")))), Word("Prop")), Equal(Div(Typed(App(Q("Nat", "card"), SubtypeOf("f", SubtypeOf("f", Call("LinearMap", App(Q("RingHom", "id"), X("K")),  X("D"), X("E")), App(Q("Function", "Injective"), X("f"))), App(X("P"), Call("imageCode", X("f"))))), R), Typed(App(Q("Nat", "card"), SubtypeOf("f", Call("LinearMap", App(Q("RingHom", "id"), X("K")),  X("D"), X("E")), App(Q("Function", "Injective"), X("f")))), R)), Div(Typed(App(Q("Nat", "card"), SubtypeOf("U", SubtypeOf("U", Call("Submodule", X("K"), X("E")), Equal(App(Q("Module", "finrank"), X("K"), X("U")), App(Q("Module", "finrank"), X("K"), X("D")))), App(X("P"), X("U")))), R), Typed(App(Q("Nat", "card"), SubtypeOf("U", Call("Submodule", X("K"), X("E")), Equal(App(Q("Module", "finrank"), X("K"), X("U")), App(Q("Module", "finrank"), X("K"), X("D"))))), R))))))))))))))))),
                DescribeRole.Theorem, AssessedProvenance.FromRepo(),
                "Every subspace of the source dimension has the same number of injective parametrizations. Therefore the proportion of maps whose image has a property equals the proportion of subspaces having that property."),
            Node("injectionFrameEquiv", "Injectionframeequiv",
                All("K", Word("Type"), Seq(OpenBracket, Call("Field", X("K")), CloseBracket, Sp, All("E", Word("Type"), Seq(OpenBracket, Call("AddCommGroup", X("E")), CloseBracket, Sp, Seq(OpenBracket, Call("Module", X("K"), X("E")), CloseBracket, Sp, All("k", Nat, And(All("f", SubtypeOf("f", Call("LinearMap", App(Q("RingHom", "id"), X("K")),  Arrow(Call("Fin", X("k")), X("K")), X("E")), App(Q("Function", "Injective"), X("f"))), Equal(Call("val", App(Call("injectionFrameEquiv", X("k")), X("f"))), Lambda("i", Call("Fin", X("k")), App(Call("val", X("f")), App(App(Q("Pi", "basisFun"), X("K"), Call("Fin", X("k"))), X("i")))))), All("v", SubtypeOf("v", Arrow(Call("Fin", X("k")), X("E")), Call("LinearIndependent", X("K"), X("v"))), Equal(Call("val", App(App(Q("Equiv", "symm"), Call("injectionFrameEquiv", X("k"))), X("v"))), App(Seq(Word("Module"), Dot, Word("Basis"), Dot, Word("constr")), App(Q("Pi", "basisFun"), X("K"), Call("Fin", X("k"))), X("K"), Call("val", X("v")))))))))))),
                DescribeRole.Definition, AssessedProvenance.FromRepo(),
                "An injective linear map corresponds to its values on the standard basis. The inverse extends an independent frame linearly using that basis."),
            Node("real_injection_count", "Real injection count",
                All("K", Word("Type"), Seq(OpenBracket, Call("Field", X("K")), CloseBracket, Sp, Seq(OpenBracket, Call("Fintype", X("K")), CloseBracket, Sp, All("E", Word("Type"), Seq(OpenBracket, Call("AddCommGroup", X("E")), CloseBracket, Sp, Seq(OpenBracket, Call("Module", X("K"), X("E")), CloseBracket, Sp, Seq(OpenBracket, Call("FiniteDimensional", X("K"), X("E")), CloseBracket, Sp, All("k", Nat, Imp(Leq(X("k"), App(Q("Module", "finrank"), X("K"), X("E"))), Equal(Typed(App(Q("Nat", "card"), SubtypeOf("f", Call("LinearMap", App(Q("RingHom", "id"), X("K")),  Arrow(Call("Fin", X("k")), X("K")), X("E")), App(Q("Function", "Injective"), X("f")))), R), ProductOn("h", App(Q("Finset", "range"), X("k")), Parenthesized(Subtract(Pow(Typed(App(Q("Fintype", "card"), X("K")), R), App(Q("Module", "finrank"), X("K"), X("E"))), Pow(Typed(App(Q("Fintype", "card"), X("K")), R), X("h"))))))))))))))),
                DescribeRole.Theorem, AssessedProvenance.FromRepo(),
                "The number of injective linear maps is the product of the choices of successive independent images of a basis."),
            Node("subspace_card_real", "Subspace card real",
                All("K", Word("Type"), Seq(OpenBracket, Call("Field", X("K")), CloseBracket, Sp, Seq(OpenBracket, Call("Fintype", X("K")), CloseBracket, Sp, All("E", Word("Type"), Seq(OpenBracket, Call("AddCommGroup", X("E")), CloseBracket, Sp, Seq(OpenBracket, Call("Module", X("K"), X("E")), CloseBracket, Sp, Seq(OpenBracket, Call("FiniteDimensional", X("K"), X("E")), CloseBracket, Sp, All("k", Nat, Imp(Leq(X("k"), App(Q("Module", "finrank"), X("K"), X("E"))), Equal(Typed(App(Q("Nat", "card"), SubtypeOf("U", Call("Submodule", X("K"), X("E")), Equal(App(Q("Module", "finrank"), X("K"), X("U")), X("k")))), R), ProductOn("h", App(Q("Finset", "range"), X("k")), Div(Parenthesized(Subtract(Pow(Typed(App(Q("Fintype", "card"), X("K")), R), App(Q("Module", "finrank"), X("K"), X("E"))), Pow(Typed(App(Q("Fintype", "card"), X("K")), R), X("h")))), Parenthesized(Subtract(Pow(Typed(App(Q("Fintype", "card"), X("K")), R), X("k")), Pow(Typed(App(Q("Fintype", "card"), X("K")), R), X("h")))))))))))))))),
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                "Page 1082 (arXiv v1): “It is well known that \\qbin{i}{j}{q} counts the number of j-dimensional subspaces of an i-dimensional space over \\F_q.” Dividing the number of independent frames by the number of their changes of basis gives the displayed product."),
            Node("annihilating_map_fraction", "Annihilating map fraction",
                All("K", Word("Type"), Seq(OpenBracket, Call("Field", X("K")), CloseBracket, Sp, Seq(OpenBracket, Call("Fintype", X("K")), CloseBracket, Sp, All("E", Word("Type"), Seq(OpenBracket, Call("AddCommGroup", X("E")), CloseBracket, Sp, Seq(OpenBracket, Call("Module", X("K"), X("E")), CloseBracket, Sp, Seq(OpenBracket, Call("FiniteDimensional", X("K"), X("E")), CloseBracket, Sp, All("F", Word("Type"), Seq(OpenBracket, Call("AddCommGroup", X("F")), CloseBracket, Sp, Seq(OpenBracket, Call("Module", X("K"), X("F")), CloseBracket, Sp, Seq(OpenBracket, Call("FiniteDimensional", X("K"), X("F")), CloseBracket, Sp, All("T", Call("Submodule", X("K"), X("E")), Equal(Div(Typed(App(Q("Nat", "card"), SubtypeOf("f", Call("LinearMap", App(Q("RingHom", "id"), X("K")),  X("E"), X("F")), Leq(X("T"), App(Q("LinearMap", "ker"), X("f"))))), R), Typed(App(Q("Nat", "card"), Call("LinearMap", App(Q("RingHom", "id"), X("K")),  X("E"), X("F"))), R)), Inverse(Pow(Typed(App(Q("Fintype", "card"), X("K")), R), Parenthesized(Mul(App(Q("Module", "finrank"), X("K"), X("T")), App(Q("Module", "finrank"), X("K"), X("F"))))))))))))))))))),
                DescribeRole.Theorem, AssessedProvenance.FromRepo(),
                "Annihilating a fixed subspace removes its dimension times the codomain dimension in the exponent of the number of linear maps."),
            Node("injective_fraction_limit", "Injective fraction limit",
                All("K", Word("Type"), Seq(OpenBracket, Call("Field", X("K")), CloseBracket, Sp, Seq(OpenBracket, Call("Fintype", X("K")), CloseBracket, Sp, All("r", Nat, All("n", Nat, Imp(Leq(D(1), X("r")), Imp(Less(X("r"), X("n")), App(Q("Filter", "Tendsto"), Lambda("m", Nat, Div(Typed(App(Q("Nat", "card"), SubtypeOf("f", Call("LinearMap", App(Q("RingHom", "id"), X("K")),  Arrow(Call("Fin", Mul(X("m"), X("r"))), X("K")), Arrow(Call("Fin", Mul(X("m"), X("n"))), X("K"))), App(Q("Function", "Injective"), X("f")))), R), Typed(App(Q("Nat", "card"), Call("LinearMap", App(Q("RingHom", "id"), X("K")),  Arrow(Call("Fin", Mul(X("m"), X("r"))), X("K")), Arrow(Call("Fin", Mul(X("m"), X("n"))), X("K")))), R))), Q("Filter", "atTop"), Call("nhds", D(1)))))))))),
                DescribeRole.Theorem, AssessedProvenance.FromRepo(),
                "If both dimensions grow linearly with the column count and the codomain grows faster, the fraction of injective maps tends to one."),
            Node("fixed_source_injection_limit", "Fixed source injection limit",
                All("K", Word("Type"), Seq(OpenBracket, Call("Field", X("K")), CloseBracket, Sp, Seq(OpenBracket, Call("Fintype", X("K")), CloseBracket, Sp, All("k", Nat, All("r", Nat, Imp(Leq(D(1), X("r")), App(Q("Filter", "Tendsto"), Lambda("m", Nat, Div(Typed(App(Q("Nat", "card"), SubtypeOf("f", Call("LinearMap", App(Q("RingHom", "id"), X("K")),  Arrow(Call("Fin", X("k")), X("K")), Arrow(Call("Fin", Mul(X("m"), X("r"))), X("K"))), App(Q("Function", "Injective"), X("f")))), R), Typed(App(Q("Nat", "card"), Call("LinearMap", App(Q("RingHom", "id"), X("K")),  Arrow(Call("Fin", X("k")), X("K")), Arrow(Call("Fin", Mul(X("m"), X("r"))), X("K")))), R))), Q("Filter", "atTop"), Call("nhds", D(1))))))))),
                DescribeRole.Theorem, AssessedProvenance.FromRepo(),
                "For a fixed source dimension and a codomain of positive linearly growing dimension, the fraction of injective maps tends to one."))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        DescribeRole role, AssessedProvenance provenance, string prose) =>
        Describe.Lean(DescribeId.Create("mrd-sampling-" + name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula X(string name) => F.Id(name);
    private static Formula Word(string name) => Seq(Operatorname, Grp(X(name)));
    private static Formula Nat => Seq(Mathbb, Grp(X("N")));
    private static Formula R => Seq(Mathbb, Grp(X("R")));
    private static Formula Q(string owner, string name) => Seq(Word(owner), Dot, Word(name));
    private static Formula App(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Subtract(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Inverse(Formula a) => new Formula.Power(a, Seq(Minus, D(1)));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, type));
    private static Formula Lambda(string name, Formula type, Formula body) => Parenthesized(Seq(Word("fun"), Sp, X(name), Colon, type, Sp, Mapsto, Sp, body));
    private static Formula ProductOn(string name, Formula domain, Formula body) => Seq(new Formula.Subscript(Prod, Seq(X(name), InMacro, Sp, domain)), Sp, body);
    private static Formula SubtypeOf(string name, Formula type, Formula body) => Seq(OpenBrace, X(name), Colon, type, Sp, Slash, Slash, Sp, body, CloseBrace);

}
