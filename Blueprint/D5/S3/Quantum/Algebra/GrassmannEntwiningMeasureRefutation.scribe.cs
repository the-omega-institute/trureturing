using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class GrassmannEntwiningMeasureRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Algebra/GrassmannEntwiningMeasureRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/adamopoulou2025entwininggrassmann");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The coefficient Jacobian of the Grassmann map S in three generators differs from the conjectured density ratio.",
        H("The invariant-measure conjecture fails in three generators"), Blocks(
            Paragraph(Text(
                "The exterior algebra ExteriorAlgebra Real (Fin 3 → Real) represents the Grassmann algebra on three generators. "
                    + "Its monomials are indexed by Finset (Fin 3), and the empty set indexes the scalar coefficient. "
                    + "A coefficient vector is a function Finset (Fin 3) → Real. "
                    + "The full coordinate space consists of functions (Finset (Fin 3) × Fin 4) → Real. "
                    + "For an even monomial, slots 0, 1, 2, 3 hold the coefficients of x₁, x₂, y₁, y₂; "
                    + "for an odd monomial they hold the coefficients of χ₁, χ₂, ψ₁, ψ₂. "
                    + "Parity is the cardinality of the monomial index modulo two, and scalar multiplication is the real module action.")),
            Node("monomialBasis", "The exterior monomial basis", MonomialBasisFormula(),
                "The standard basis of Fin 3 → Real induces the monomial basis of the exterior algebra. "
                    + "A finite subset specifies the ordered product of its generators, including the empty product 1.",
                AssessedProvenance.FromRepo(Source)),
            Node("coord", "The coefficient equivalence", CoordFormula(),
                "Module.Basis.equivFun gives the real linear equivalence from exterior elements to their monomial coefficients.",
                AssessedProvenance.FromRepo(Source)),
            Node("unitC", "The coordinates of the unit", UnitFormula(),
                "The algebraic unit has scalar coefficient 1 and every nonempty monomial coefficient 0.",
                AssessedProvenance.FromRepo(Source)),
            Node("gmul", "The exterior product in coordinates", ProductFormula(),
                "Section 2.1 specifies the Grassmann product by anticommutation of the generators. "
                    + "The displayed product decodes two coefficient vectors, multiplies in ExteriorAlgebra, and takes coordinates again.",
                AssessedProvenance.FromLiterature(Source)),
            Node("ginv", "The inverse of an even element", InverseFormula(),
                "For an even element with nonzero scalar coefficient c, the positive-degree part has square zero in three generators. "
                    + "Its two-sided inverse is c⁻¹ times the unit minus c⁻² times that positive-degree part. "
                    + "The displayed definition is a total function on coefficient vectors; the inverse interpretation requires even parity and c ≠ 0.",
                AssessedProvenance.FromLiterature(Source)),
            Node("pick", "Selecting a parity and a slot", PickFormula(),
                "The continuous real linear map selects slot j on monomials of parity p and sets all other coefficients to zero. "
                    + "Here p is any natural number, so p outside {0,1} gives the zero map.",
                AssessedProvenance.FromRepo(Source)),
            Node("pack", "Packing the two parities", PackFormula(),
                "For each monomial and slot, the packed vector reads the corresponding even or odd coefficient according to monomial parity.",
                AssessedProvenance.FromRepo(Source)),
            Node("ratio", "The even quotient y₁ over x₁", RatioFormula(),
                "This coefficient vector is the product of y₁ with the explicit inverse of x₁.",
                AssessedProvenance.FromRepo(Source)),
            Node("evenOut", "The four even components of equation (18)", EvenFormula(),
                "The four entries are u₁, u₂, v₁, v₂, in that order. "
                    + "They reproduce the even equations of the source's S map, with real parameters a and b acting by scalar multiplication. "
                    + "Each nested product follows the order of the factors in equation (18).",
                AssessedProvenance.FromLiterature(Source)),
            Node("oddOut", "The four odd components of equation (18)", OddFormula(),
                "The four entries are ξ₁, ξ₂, η₁, η₂, in that order: "
                    + "ψ₁ − (y₁/x₁)χ₁, ψ₂, χ₁, and χ₂ + (y₁/x₁)ψ₂.",
                AssessedProvenance.FromLiterature(Source)),
            Node("F", "The full coefficient map", MapFormula(),
                "Equation (18) is evaluated in monomial coefficients. "
                    + "Quotients by even elements with nonzero scalar coefficient are products with their two-sided inverse. "
                    + "The output coordinates use the same (monomial, slot) layout as the inputs, "
                    + "with even slots u₁, u₂, v₁, v₂ and odd slots ξ₁, ξ₂, η₁, η₂.",
                AssessedProvenance.FromLiterature(Source)),
            Node("domain", "Nonzero scalar denominators", DomainFormula(),
                "The scalar coefficients of x₁ and y₁ are nonzero. "
                    + "At b = 2 these are exactly the nonzero scalar denominators needed by equation (18).",
                AssessedProvenance.FromRepo(Source)),
            Node("m", "The proposed density in three generators", DensityFormula(),
                "The conjecture in Section 5 proposes the inverse cube of the scalar coefficient of y₁ for the S map in three generators.",
                AssessedProvenance.FromLiterature(Source)),
            Node("jacobian", "The coefficient Jacobian determinant", JacobianFormula(),
                "Section 4 defines J as the ordinary Jacobian determinant of the map on commuting coefficients. "
                    + "Here fderiv is the real Fréchet derivative and LinearMap.det takes its determinant.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The conjectured density identity", ClaimFormula(),
                "At a = 1 and b = 2, the S clause of the Section 5 conjecture would give the Section 4 identity "
                    + "J(z) = m(z)/m(S(z)) at every point with nonzero scalar denominators.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("grassmann-measure-result"), DeclarationHandle.Create(Prefix + "result"),
                H("A scalar counterexample"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Take a = 1, b = 2, and scalar coefficients (x₁, x₂, y₁, y₂) = (1,3,2,4), "
                            + "with all other coefficients zero. Both scalar denominators are nonzero. "
                            + "The derivative preserves each monomial index and is block diagonal. "
                            + "Each of the four even monomials has a four-by-four block of determinant 1/2, "
                            + "and each of the four odd monomials has a block of determinant 1.")),
                    Paragraph(Text(
                        "Thus the coefficient Jacobian is J = (1/2)⁴ = 1/16. "
                            + "The scalar coefficient of the output v₁ is 1, so the density ratio is m(z)/m(S(z)) = 1/8. "
                            + "These unequal values refute the stated identity."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("adamopoulou-papamikos-2025-grassmann-measure-refutation"),
                    ResolutionKind.Refuted))
        )));

    private static DocumentBlock Node(string declaration, string title, Formula formula,
        string prose, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("grassmann-measure-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula MonomialBasisFormula() => Equal(
        Typed(Local("monomialBasis"), At(Qualified("Module", "Basis"), Monomials(), Reals(), Grassmann())),
        At(Qualified("Module", "Basis", "ExteriorAlgebra"),
            At(Qualified("Pi", "basisFun"), Reals(), FinOf(3))));

    private static Formula CoordFormula() => Equal(
        Typed(Local("coord"), At(Qualified("LinearEquiv"),
            At(Qualified("RingHom", "id"), Reals()), Grassmann(), Coefficients())),
        At(Qualified("Module", "Basis", "equivFun"), Local("monomialBasis")));

    private static Formula UnitFormula() => Equal(Typed(Local("unitC"), Coefficients()),
        LocalCall("coord", Typed(D(1), Grassmann())));

    private static Formula ProductFormula() => All("u", Coefficients(), All("v", Coefficients(),
        Equal(Typed(LocalCall("gmul", V("u"), V("v")), Coefficients()),
            LocalCall("coord", Multiply(
                At(Qualified("LinearEquiv", "symm"), Local("coord"), V("u")),
                At(Qualified("LinearEquiv", "symm"), Local("coord"), V("v")))))));

    private static Formula InverseFormula()
    {
        Formula scalar = At(V("u"), Emptyset);
        Formula inverse = Power(scalar, Seq(Minus, D(1)));
        return All("u", Coefficients(), Equal(Typed(LocalCall("ginv", V("u")), Coefficients()),
            Subtract(Smul(inverse, Local("unitC")),
                Smul(Power(inverse, D(2)), Subtract(V("u"), Smul(scalar, Local("unitC")))))));
    }

    private static Formula PickFormula() => All("p", Naturals(), All("j", FinOf(4),
        Equal(Typed(LocalCall("pick", V("p"), V("j")), ContinuousArrow(CoordinateSpace(), Coefficients())),
            At(Qualified("ContinuousLinearMap", "pi"), LambdaOf("s", Monomials(),
                At(Qualified("ite"), Parenthesized(Equal(Parity(V("s")), V("p"))),
                    At(Qualified("ContinuousLinearMap", "proj"), Pair(V("s"), V("j"))),
                    Typed(D(0), ContinuousArrow(CoordinateSpace(), Reals()))))))));

    private static Formula PackFormula()
    {
        Formula monomial = At(Qualified("Prod", "fst"), V("i"));
        Formula slot = At(Qualified("Prod", "snd"), V("i"));
        return All("e", Outputs(), All("o", Outputs(),
            Equal(Typed(LocalCall("pack", V("e"), V("o")), CoordinateSpace()),
                LambdaOf("i", CoordinateIndex(), At(Qualified("ite"),
                    Parenthesized(Equal(Parity(monomial), D(0))),
                    At(V("e"), slot, monomial), At(V("o"), slot, monomial))))));
    }

    private static Formula RatioFormula() => All("z", CoordinateSpace(),
        Equal(Typed(LocalCall("ratio", V("z")), Coefficients()),
            GrassmannProduct(Pick(0, 2), LocalCall("ginv", Pick(0, 0)))));

    private static Formula EvenFormula()
    {
        Formula first = Add(
            GrassmannProduct(
                GrassmannProduct(GrassmannProduct(Pick(0, 2), Pick(0, 2)),
                    Add(Local("unitC"), GrassmannProduct(Pick(1, 0), Pick(1, 3)))),
                LocalCall("ginv", Smul(V("b"), Pick(0, 0)))),
            Smul(Power(V("b"), Seq(Minus, D(1))), GrassmannProduct(Pick(0, 2),
                Subtract(Subtract(Pick(0, 3), Smul(V("a"), Local("unitC"))),
                    GrassmannProduct(Pick(1, 2), Pick(1, 3))))));
        Formula second = Smul(V("b"), LocalCall("ginv", Pick(0, 2)));
        Formula fourth = Add(Subtract(Add(Smul(V("a"), Local("unitC")),
            GrassmannProduct(Pick(0, 0), Pick(0, 1))), LocalCall("ratio", V("z"))),
            GrassmannProduct(Pick(1, 0), Pick(1, 1)));
        return MapBinders(Equal(Typed(LocalCall("evenOut", V("a"), V("b"), V("z")), Outputs()),
            Vector(first, second, Pick(0, 0), fourth)));
    }

    private static Formula OddFormula() => All("z", CoordinateSpace(),
        Equal(Typed(LocalCall("oddOut", V("z")), Outputs()), Vector(
            Subtract(Pick(1, 2), GrassmannProduct(LocalCall("ratio", V("z")), Pick(1, 0))),
            Pick(1, 3), Pick(1, 0),
            Add(Pick(1, 1), GrassmannProduct(LocalCall("ratio", V("z")), Pick(1, 3))))));

    private static Formula MapFormula() => MapBinders(
        Equal(Typed(LocalCall("F", V("a"), V("b"), V("z")), CoordinateSpace()),
            LocalCall("pack", LocalCall("evenOut", V("a"), V("b"), V("z")),
                LocalCall("oddOut", V("z")))));

    private static Formula DomainFormula() => All("z", CoordinateSpace(),
        Iff(LocalCall("domain", V("z")), And(
            NotEqual(At(V("z"), Pair(Emptyset, D(0))), D(0)),
            NotEqual(At(V("z"), Pair(Emptyset, D(2))), D(0)))));

    private static Formula DensityFormula() => All("z", CoordinateSpace(),
        Equal(Typed(LocalCall("m", V("z")), Reals()),
            Power(Power(At(V("z"), Pair(Emptyset, D(2))), D(3)), Seq(Minus, D(1)))));

    private static Formula JacobianFormula() => MapBinders(
        Equal(Typed(LocalCall("jacobian", V("a"), V("b"), V("z")), Reals()),
            At(Qualified("LinearMap", "det"), At(Qualified("ContinuousLinearMap", "toLinearMap"),
                At(Qualified("fderiv"), Reals(), LocalCall("F", V("a"), V("b")), V("z"))))));

    private static Formula ClaimFormula() => Iff(Local("claim"), All("z", CoordinateSpace(),
        Imp(LocalCall("domain", V("z")), Equal(LocalCall("jacobian", D(1), D(2), V("z")),
            new Formula.Fraction(LocalCall("m", V("z")), LocalCall("m", LocalCall("F", D(1), D(2), V("z"))))))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(V(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum", "Algebra",
        "GrassmannEntwiningMeasureRefutation", name);
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Reals() => Seq(Mathbb, Grp(V("R")));
    private static Formula Naturals() => Seq(Mathbb, Grp(V("N")));
    private static Formula FinOf(byte n) => At(Qualified("Fin"), D(n));
    private static Formula Monomials() => At(Qualified("Finset"), FinOf(3));
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(domain, codomain);
    private static Formula Coefficients() => Parenthesized(Arrow(Monomials(), Reals()));
    private static Formula Grassmann() => At(Qualified("ExteriorAlgebra"), Reals(), Arrow(FinOf(3), Reals()));
    private static Formula CoordinateIndex() => Parenthesized(Seq(Monomials(), Sp, Times, Sp, FinOf(4)));
    private static Formula CoordinateSpace() => Parenthesized(Arrow(CoordinateIndex(), Reals()));
    private static Formula Outputs() => Parenthesized(Arrow(FinOf(4), Coefficients()));
    private static Formula ContinuousArrow(Formula domain, Formula codomain) => At(Qualified("ContinuousLinearMap"),
        At(Qualified("RingHom", "id"), Reals()), domain, codomain);
    private static Formula Pair(Formula left, Formula right) => Parenthesized(Seq(left, Comma, Sp, right));
    private static Formula Parity(Formula monomial) => new Formula.Modulo(At(Qualified("Finset", "card"), monomial), D(2));
    private static Formula Pick(byte parity, byte slot) => LocalCall("pick", D(parity), D(slot), V("z"));
    private static Formula GrassmannProduct(Formula left, Formula right) => LocalCall("gmul", left, right);
    private static Formula Vector(Formula first, Formula second, Formula third, Formula fourth) =>
        Seq(Bang, OpenBracket, first, Comma, Sp, second, Comma, Sp, third, Comma, Sp, fourth, CloseBracket);
    private static Formula MapBinders(Formula body) => All("a", Reals(), All("b", Reals(), All("z", CoordinateSpace(), body)));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(V(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Smul(Formula scalar, Formula vector) => Seq(Parenthesized(scalar), Sp, Cdot, Sp, Parenthesized(vector));
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(Parenthesized(value), exponent);
    private static Formula Multiply(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Subtract(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
